{-# LANGUAGE MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
            ,FlexibleContexts
            ,GeneralizedNewtypeDeriving
            ,TypeSynonymInstances
            ,TypeOperators
            ,ParallelListComp
            ,BangPatterns
 #-}
{-# OPTIONS -cpp #-}






{-|

Funsat aims to be a reasonably efficient modern SAT solver that is easy to
integrate as a backend to other projects.  SAT is NP-complete, and thus has
reductions from many other interesting problems.  We hope this implementation is
efficient enough to make it useful to solve medium-size, real-world problem
mapped from another space.  We also have taken pains test the solver rigorously
to encourage confidence in its output.

One particular nicetie facilitating integration of Funsat into other projects
is the efficient calculation of an /unsatisfiable core/ for unsatisfiable
problems (see the "Funsat.Resolution" module).  In the case a problem is
unsatisfiable, as a by-product of checking the proof of unsatisfiability,
Funsat will generate a minimal set of input clauses that are also
unsatisfiable.

Another is the ability to compile high-level circuits into CNF.  Seen the
"Funsat.Circuit" module.

* 07 Jun 2008 21:43:42: N.B. because of the use of mutable arrays in the ST
monad, the solver will actually give _wrong_ answers if you compile without
optimisation.  Which is okay, 'cause that's really slow anyway.

[@Bibliography@]

  * ''Abstract DPLL and DPLL Modulo Theories''

  * ''Chaff: Engineering an Efficient SAT solver''

  * ''An Extensible SAT-solver'' by Niklas Een, Niklas Sorensson

  * ''Efficient Conflict Driven Learning in a Boolean Satisfiability Solver''
by Zhang, Madigan, Moskewicz, Malik

  * ''SAT-MICRO: petit mais costaud!'' by Conchon, Kanig, and Lescuyer

-}
module Funsat.Solver
#ifndef TESTING
        ( -- * Interface
          solve
        , solve1
        , Solution(..)
          -- ** Verification
        , verify
        , VerifyError(..)
          -- ** Configuration
        , FunsatConfig(..)
        , defaultConfig
          -- * Solver statistics
        , Stats(..)
        , ShowWrapped(..)
        , statTable
        , statSummary
        )
#endif
    where

{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}


import Control.Arrow( (&&&) )
import Control.Exception( assert )
import Control.Monad.Error hiding ( (>=>), forM_, runErrorT )
import Control.Monad.MonadST( MonadST(..) )
import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ( (>=>), forM_ )
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable hiding ( sequence_ )
import Data.Int( Int64 )
import Data.List( nub, tails, sortBy, sort )
import Data.Maybe
import Data.Ord( comparing )
import Data.STRef
import Data.Sequence( Seq )
-- import Debug.Trace (trace)
import Funsat.Monad
import Funsat.Utils
import Funsat.Resolution( ResolutionTrace(..), initResolutionTrace )
import Funsat.Types
import Funsat.Types.Internal
import Prelude hiding ( sum, concatMap, elem, foldr, foldl, any, maximum )
import Funsat.Resolution( ResolutionError(..) )
import Text.Printf( printf )
import qualified Data.Foldable as Fl
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Funsat.Resolution as Resolution
import qualified Text.Tabular as Tabular

-- * Interface

-- | Run the DPLL-based SAT solver on the given CNF instance.  Returns a
-- solution, along with internal solver statistics and possibly a resolution
-- trace.  The trace is for checking a proof of `Unsat', and thus is only
-- present when the result is `Unsat'.
solve :: FunsatConfig -> CNF -> (Solution, Stats, Maybe ResolutionTrace)
solve cfg fIn =
    -- To solve, we simply take baby steps toward the solution using solveStep,
    -- starting with an initial assignment.
--     trace ("input " ++ show f) $
    either (error "solve: invariant violated") id $
    runST $
    evalSSTErrMonad
        (do initialAssignment <- liftST $ newSTUArray (V 1, V (numVars f)) 0
            (a, isUnsat) <- initialState initialAssignment
            if isUnsat then reportSolution (Unsat a)
                       else stepToSolution initialAssignment >>= reportSolution)
    SC{ cnf = f{ clauses = Set.empty }, dl = []
      , watches = undefined, learnt = undefined
      , propQ = Seq.empty, trail = [], level = undefined
      , stats = FunStats{numConfl = 0,numConflTotal = 0,numDecisions = 0,numImpl = 0}
      , reason = Map.empty, varOrder = undefined
      , resolutionTrace = PartialResolutionTrace 1 [] [] Map.empty
      , dpllConfig = cfg }
  where
    f = preprocessCNF fIn
    -- If returns True, then problem is unsat.
    initialState :: MAssignment s -> FunMonad s (IAssignment, Bool)
    initialState m = do
      initialLevel <- liftST $ newSTUArray (V 1, V (numVars f)) noLevel
      modify $ \s -> s{ level = initialLevel }
      initialWatches <- liftST $ newSTArray (L (- (numVars f)), L (numVars f)) []
      modify $ \s -> s{ watches = initialWatches }
      initialLearnts <- liftST $ newSTArray (L (- (numVars f)), L (numVars f)) []
      modify $ \s -> s{ learnt = initialLearnts }
      initialVarOrder <- liftST $ newSTUArray (V 1, V (numVars f)) initialActivity
      modify $ \s -> s{ varOrder = VarOrder initialVarOrder }

      -- Watch each clause, making sure to bork if we find a contradiction.
      (`catchError`
       (const $ liftST (unsafeFreezeAss m) >>= \a -> return (a,True))) $ do
          forM_ (clauses f)
            (\c -> do cid <- nextTraceId
                      isConsistent <- watchClause m (c, cid) False
                      when (not isConsistent)
                        -- conflict data is ignored here, so safe to fake
                        (do traceClauseId cid ; throwError (L 0, [], 0)))
          a <- liftST (unsafeFreezeAss m)
          return (a, False)


-- | Solve with the default configuration `defaultConfig'.
solve1 :: CNF -> (Solution, Stats, Maybe ResolutionTrace)
solve1 = solve defaultConfig

-- | This function applies `solveStep' recursively until SAT instance is
-- solved, starting with the given initial assignment.  It also implements the
-- conflict-based restarting (see `FunsatConfig').
stepToSolution :: MAssignment s -> FunMonad s Solution
stepToSolution assignment = do
    step <- solveStep assignment
    useRestarts <- gets (configUseRestarts . dpllConfig)
    isTimeToRestart <- uncurry ((>=)) `liftM`
               gets ((numConfl . stats) &&& (configRestart . dpllConfig))
    case step of
      Left m -> do when (useRestarts && isTimeToRestart)
                     (do _stats <- extractStats
--                          trace ("Restarting...") $
--                           trace (statSummary stats) $
                         resetState m)
                   stepToSolution m
      Right s -> return s
  where
    resetState m = do
      modify $ \s -> let st = stats s in s{ stats = st{numConfl = 0} }
      -- Require more conflicts before next restart.
      modifySlot dpllConfig $ \s c ->
        s{ dpllConfig = c{ configRestart = ceiling (configRestartBump c
                                                   * fromIntegral (configRestart c))
                           } }
      lvl :: FrozenLevelArray <- gets level >>= liftST . unsafeFreeze
      undoneLits <- takeWhile (\l -> lvl ! (var l) > 0) `liftM` gets trail
      forM_ undoneLits $ const (undoOne m)
      modify $ \s -> s{ dl = [], propQ = Seq.empty }
      compactDB
      unsafeFreezeAss m >>= simplifyDB

reportSolution :: Solution -> FunMonad s (Solution, Stats, Maybe ResolutionTrace)
reportSolution s = do
    stats <- extractStats
    case s of
      Sat _   -> return (s, stats, Nothing)
      Unsat _ -> do
          resTrace <- constructResTrace s
          return (s, stats, Just resTrace)


-- | A default configuration based on the formula to solve.
--
--  * restarts every 100 conflicts
--
--  * requires 1.5 as many restarts after restarting as before, each time
--
--  * VSIDS to be enabled
--
--  * restarts to be enabled
defaultConfig :: FunsatConfig
defaultConfig = Cfg { configRestart = 100 -- fromIntegral $ max (numVars f `div` 10) 100
                      , configRestartBump = 1.5
                      , configUseVSIDS = True
                      , configUseRestarts = True }

-- * Preprocessing

-- | Some kind of preprocessing.
--
--   * remove duplicates
preprocessCNF :: CNF -> CNF
preprocessCNF f = f{clauses = simpClauses (clauses f)}
    where simpClauses = Set.map nub -- rm dups

-- | Simplify the clause database.  Eventually should supersede, probably,
-- `preprocessCNF'.
--
-- Precondition: decision level 0.
simplifyDB :: IAssignment -> FunMonad s ()
simplifyDB mFr = do
  -- For each clause in the database, remove it if satisfied; if it contains a
  -- literal whose negation is assigned, delete that literal.
  n <- numVars `liftM` gets cnf
  s <- get
  liftST . forM_ [V 1 .. V n] $ \i -> when (mFr!i /= 0) $ do
    let l = L (mFr!i)
        filterL _i = map (\(p, c, cid) -> (p, filter (/= negate l) c, cid))
    -- Remove unsat literal `negate l' from clauses.
--     modifyArray (watches s) l filterL
    modifyArray (learnt s) l filterL
    -- Clauses containing `l' are Sat.
--     writeArray (watches s) (negate l) []
    writeArray (learnt s) (negate l) []

-- * Internals

-- | The DPLL procedure is modeled as a state transition system.  This
-- function takes one step in that transition system.  Given an unsatisfactory
-- assignment, perform one state transition, producing a new assignment and a
-- new state.
solveStep :: MAssignment s -> FunMonad s (Either (MAssignment s) Solution)
solveStep m = do
    unsafeFreezeAss m >>= solveStepInvariants
    conf <- gets dpllConfig
    let selector = if configUseVSIDS conf then select else selectStatic
    maybeConfl <- bcp m
    mFr   <- unsafeFreezeAss m
    voArr <- gets (varOrderArr . varOrder)
    voFr  <- FrozenVarOrder `liftM` liftST (unsafeFreeze voArr)
    s     <- get
    stepForward $ 
          -- Check if unsat.
          unsat maybeConfl s ==> postProcessUnsat maybeConfl
          -- Unit propagation may reveal conflicts; check.
       >< maybeConfl         >=> backJump m
          -- No conflicts.  Decide.
       >< selector mFr voFr  >=> decide m
    where
      -- Take the step chosen by the transition guards above.
      stepForward Nothing     = (Right . Sat) `liftM` unsafeFreezeAss m
      stepForward (Just step) = do
          r <- step
          case r of
            Nothing -> (Right . Unsat) `liftM` liftST (unsafeFreezeAss m)
            Just m  -> return . Left $ m

-- | /Precondition:/ problem determined to be unsat.
--
-- Records id of conflicting clause in trace before failing.  Always returns
-- `Nothing'.
postProcessUnsat :: Maybe (Lit, Clause, ClauseId) -> FunMonad s (Maybe a)
postProcessUnsat maybeConfl = do
    traceClauseId $ (thd . fromJust) maybeConfl
    return Nothing
  where
    thd (_,_,i) = i

-- | Check data structure invariants.  Unless @-fno-ignore-asserts@ is passed,
-- this should be optimised away to nothing.
solveStepInvariants :: IAssignment -> FunMonad s ()
{-# INLINE solveStepInvariants #-}
solveStepInvariants _m = assert True $ do
    s <- get
    -- no dups in decision list or trail
    assert ((length . dl) s == (length . nub . dl) s) $
     assert ((length . trail) s == (length . nub . trail) s) $
     return ()

-- ** Internals

-- | Value of the `level' array if corresponding variable unassigned.  Had
-- better be less that 0.
noLevel :: Level
noLevel = -1


-- *** Boolean constraint propagation

-- | Assign a new literal, and enqueue any implied assignments.  If a conflict
-- is detected, return @Just (impliedLit, conflictingClause)@; otherwise
-- return @Nothing@.  The @impliedLit@ is implied by the clause, but conflicts
-- with the assignment.
--
-- If no new clauses are unit (i.e. no implied assignments), simply update
-- watched literals.
bcpLit :: MAssignment s
          -> Lit                -- ^ Assigned literal which might propagate.
          -> FunMonad s (Maybe (Lit, Clause, ClauseId))
bcpLit m l = do
    ws <- gets watches ; ls <- gets learnt
    clauses <- liftST $ readArray ws l
    learnts <- liftST $ readArray ls l
    liftST $ do writeArray ws l [] ; writeArray ls l []

    -- Update wather lists for normal & learnt clauses; if conflict is found,
    -- return that and don't update anything else.
    (`catchError` return . Just) $ do
      {-# SCC "bcpWatches" #-} forM_ (tails clauses) (updateWatches
        (\ f l -> liftST $ modifyArray ws l (const f)))
      {-# SCC "bcpLearnts" #-} forM_ (tails learnts) (updateWatches
        (\ f l -> liftST $ modifyArray ls l (const f)))
      return Nothing            -- no conflict
  where
    -- updateWatches: `l' has been assigned, so we look at the clauses in
    -- which contain @negate l@, namely the watcher list for l.  For each
    -- annotated clause, find the status of its watched literals.  If a
    -- conflict is found, the at-fault clause is returned through Left, and
    -- the unprocessed clauses are placed back into the appropriate watcher
    -- list.
    {-# INLINE updateWatches #-}
    updateWatches _ [] = return ()
    updateWatches alter (annCl@(watchRef, c, cid) : restClauses) = do
      mFr <- unsafeFreezeAss m
      q   <- liftST $ do (x, y) <- readSTRef watchRef
                         return $ if x == l then y else x
      -- l,q are the (negated) literals being watched for clause c.
      if negate q `isTrueUnder` mFr -- if other true, clause already sat
       then alter (annCl:) l
       else
         case find (\x -> x /= negate q && x /= negate l
                          && not (x `isFalseUnder` mFr)) c of
           Just l' -> do     -- found unassigned literal, negate l', to watch
             liftST $ writeSTRef watchRef (q, negate l')
             alter (annCl:) (negate l')

           Nothing -> do      -- all other lits false, clause is unit
             incNumImpl
             alter (annCl:) l
             isConsistent <- enqueue m (negate q) (Just (c, cid))
             when (not isConsistent) $ do -- unit literal is conflicting
                alter (restClauses ++) l
                clearQueue
                throwError (negate q, c, cid)

-- | Boolean constraint propagation of all literals in `propQ'.  If a conflict
-- is found it is returned exactly as described for `bcpLit'.
bcp :: MAssignment s -> FunMonad s (Maybe (Lit, Clause, ClauseId))
bcp m = do
  q <- gets propQ
  if Seq.null q then return Nothing
   else do
     p <- dequeue
     bcpLit m p >>= maybe (bcp m) (return . Just)



-- *** Decisions

-- | Find and return a decision variable.  A /decision variable/ must be (1)
-- undefined under the assignment and (2) it or its negation occur in the
-- formula.
--
-- Select a decision variable, if possible, and return it and the adjusted
-- `VarOrder'.
select :: IAssignment -> FrozenVarOrder -> Maybe Var
{-# INLINE select #-}
select = varOrderGet

selectStatic :: IAssignment -> a -> Maybe Var
{-# INLINE selectStatic #-}
selectStatic m _ = find (`isUndefUnder` m) (range . bounds $ m)

-- | Assign given decision variable.  Records the current assignment before
-- deciding on the decision variable indexing the assignment.
decide :: MAssignment s -> Var -> FunMonad s (Maybe (MAssignment s))
decide m v = do
  let ld = L (unVar v)
  (SC{dl=dl}) <- get
--   trace ("decide " ++ show ld) $ return ()
  incNumDecisions
  modify $ \s -> s{ dl = ld:dl }
  enqueue m ld Nothing
  return $ Just m



-- *** Backtracking

-- | Non-chronological backtracking.  The current returns the learned clause
-- implied by the first unique implication point cut of the conflict graph.
backJump :: MAssignment s
         -> (Lit, Clause, ClauseId)
            -- ^ @(l, c)@, where attempting to assign @l@ conflicted with
            -- clause @c@.
         -> FunMonad s (Maybe (MAssignment s))
backJump m c@(_, _conflict, _) = get >>= \(SC{dl=dl, reason=_reason}) -> do
    _theTrail <- gets trail
--     trace ("********** conflict = " ++ show c) $ return ()
--     trace ("trail = " ++ show _theTrail) $ return ()
--     trace ("dlits (" ++ show (length dl) ++ ") = " ++ show dl) $ return ()
--          ++ "reason: " ++ Map.showTree _reason
--           ) (
    incNumConfl ; incNumConflTotal
    levelArr :: FrozenLevelArray <- do s <- get
                                       liftST $ unsafeFreeze (level s)
    (learntCl, learntClId, newLevel) <-
        do mFr <- unsafeFreezeAss m
           analyse mFr levelArr dl c
    s <- get
    let numDecisionsToUndo = length dl - newLevel
        dl' = drop numDecisionsToUndo dl
        undoneLits = takeWhile (\lit -> levelArr ! (var lit) > newLevel) (trail s) 
    forM_ undoneLits $ const (undoOne m) -- backtrack
    mFr <- unsafeFreezeAss m
    assert (numDecisionsToUndo > 0) $
     assert (not (null learntCl)) $
     assert (learntCl `isUnitUnder` mFr) $
     modify $ \s -> s{ dl  = dl' } -- undo decisions
    mFr <- unsafeFreezeAss m
--     trace ("new mFr: " ++ showAssignment mFr) $ return ()
    -- TODO once I'm sure this works I don't need getUnit, I can just use the
    -- uip of the cut.
    watchClause m (learntCl, learntClId) True
    enqueue m (getUnit learntCl mFr) (Just (learntCl, learntClId))
      -- learntCl is asserting
    return $ Just m



-- | @doWhile cmd test@ first runs @cmd@, then loops testing @test@ and
-- executing @cmd@.  The traditional @do-while@ semantics, in other words.
doWhile :: (Monad m) => m () -> m Bool -> m ()
doWhile body test = do
  body
  shouldContinue <- test
  when shouldContinue $ doWhile body test

-- | Analyse a the conflict graph and produce a learned clause.  We use the
-- First UIP cut of the conflict graph.
--
-- May undo part of the trail, but not past the current decision level.
analyse :: IAssignment -> FrozenLevelArray -> [Lit] -> (Lit, Clause, ClauseId)
        -> FunMonad s (Clause, ClauseId, Int)
           -- ^ learned clause and new decision level
analyse mFr levelArr dlits (cLit, cClause, cCid) = do
    st <- get
--     trace ("mFr: " ++ showAssignment mFr) $ assert True (return ())
--     let (learntCl, newLevel) = cutLearn mFr levelArr firstUIPCut
--         firstUIPCut = uipCut dlits levelArr conflGraph (unLit cLit)
--                       (firstUIP conflGraph)
--         conflGraph = mkConflGraph mFr levelArr (reason st) dlits c
--                      :: Gr CGNodeAnnot ()
--     trace ("graphviz graph:\n" ++ graphviz' conflGraph) $ return ()
--     trace ("cut: " ++ show firstUIPCut) $ return ()
--     trace ("topSort: " ++ show topSortNodes) $ return ()
--     trace ("dlits (" ++ show (length dlits) ++ "): " ++ show dlits) $ return ()
--     trace ("learnt: " ++ show (map (\l -> (l, levelArr!(var l))) learntCl, newLevel)) $ return ()
--     outputConflict "conflict.dot" (graphviz' conflGraph) $ return ()
--     return $ (learntCl, newLevel)
    m <- liftST $ unsafeThawAss mFr
    a <- firstUIPBFS m (numVars . cnf $ st) (reason st)
--     trace ("firstUIPBFS learned: " ++ show a) $ return ()
    return a
  where
    -- BFS by undoing the trail backward.  From Minisat paper.  Returns
    -- conflict clause and backtrack level.
    firstUIPBFS :: MAssignment s -> Int -> ReasonMap
                -> FunMonad s (Clause, ClauseId, Int)
    firstUIPBFS m nVars reasonMap =  do
      resolveSourcesR <- liftST $ newSTRef [] -- trace sources
      let addResolveSource clauseId =
              liftST $ modifySTRef resolveSourcesR (clauseId:)
      -- Literals we should process.
      seenArr  <- liftST $ newSTUArray (V 1, V nVars) False
      counterR <- liftST $ newSTRef (0 :: Int) -- Number of unprocessed current-level
                                               -- lits we know about.
      pR <- liftST $ newSTRef cLit -- Invariant: literal from current dec. lev.
      out_learnedR <- liftST $ newSTRef []
      out_btlevelR <- liftST $ newSTRef 0
      let reasonL l = if l == cLit then (cClause, cCid)
                      else
                        let (r, rid) =
                                Map.findWithDefault (error "analyse: reasonL")
                                (var l) reasonMap
                        in (r `without` l, rid)


      (`doWhile` (liftM (> 0) (liftST $ readSTRef counterR))) $
        do p <- liftST $ readSTRef pR
           let (p_reason, p_rid) = reasonL p
           traceClauseId p_rid
           addResolveSource p_rid
           forM_ p_reason (bump . var)
           -- For each unseen reason,
           -- > from the current level, bump counter
           -- > from lower level, put in learned clause
           liftST . forM_ p_reason $ \q -> do
             seenq <- readArray seenArr (var q)
             when (not seenq) $
               do writeArray seenArr (var q) True
                  if levelL q == currentLevel
                   then modifySTRef counterR (+ 1)
                   else if levelL q > 0
                   then do modifySTRef out_learnedR (q:)
                           modifySTRef out_btlevelR $ max (levelL q)
                   else return ()
           -- Select next literal to look at:
           (`doWhile` (liftST (readSTRef pR >>= readArray seenArr . var)
                       >>= return . not)) $ do
             p <- head `liftM` gets trail -- a dec. var. only if the counter =
                                          -- 1, i.e., loop terminates now
             liftST $ writeSTRef pR p
             undoOne m
           -- Invariant states p is from current level, so when we're done
           -- with it, we've thrown away one lit. from counting toward
           -- counter.
           liftST $ modifySTRef counterR (\c -> c - 1)
      p <- liftST $ readSTRef pR
      liftST $ modifySTRef out_learnedR (negate p:)
      bump . var $ p
      out_learned <- liftST $ readSTRef out_learnedR
      out_btlevel <- liftST $ readSTRef out_btlevelR
      learnedClauseId <- nextTraceId
      storeResolvedSources resolveSourcesR learnedClauseId
      traceClauseId learnedClauseId
      return (out_learned, learnedClauseId, out_btlevel)

    -- helpers
    currentLevel = length dlits
    levelL l = levelArr!(var l)
    storeResolvedSources rsR clauseId = do
      rsReversed <- liftST $ readSTRef rsR
      modifySlot resolutionTrace $ \s rt ->
        s{resolutionTrace =
              rt{resSourceMap =
                     Map.insert clauseId (reverse rsReversed) (resSourceMap rt)}}


-- | Delete the assignment to last-assigned literal.  Undoes the trail, the
-- assignment, sets `noLevel', undoes reason.
--
-- Does /not/ touch `dl'.
undoOne :: MAssignment s -> FunMonad s ()
{-# INLINE undoOne #-}
undoOne m = do
    trl <- gets trail
    lvl <- gets level
    case trl of
      []       -> error "undoOne of empty trail"
      (l:trl') -> do
          liftST $ m `unassign` l
          liftST $ writeArray lvl (var l) noLevel
          modify $ \s ->
            s{ trail    = trl'
             , reason   = Map.delete (var l) (reason s) }

-- | Increase the recorded activity of given variable.
bump :: Var -> FunMonad s ()
{-# INLINE bump #-}
bump v = varOrderMod v (+ varInc)

-- | Constant amount by which a variable is `bump'ed.
varInc :: Double
varInc = 1.0
  


-- *** Impossible to satisfy

-- | /O(1)/.  Test for unsatisfiability.
--
-- The DPLL paper says, ''A problem is unsatisfiable if there is a conflicting
-- clause and there are no decision literals in @m@.''  But we were deciding
-- on all literals *without* creating a conflicting clause.  So now we also
-- test whether we've made all possible decisions, too.
unsat :: Maybe a -> FunsatState s -> Bool
{-# INLINE unsat #-}
unsat maybeConflict (SC{dl=dl}) = isUnsat
    where isUnsat = (null dl && isJust maybeConflict)
                    -- or BitSet.size bad == numVars cnf



-- ** Helpers

-- *** Clause compaction

-- | Keep the smaller half of the learned clauses.
compactDB :: FunMonad s ()
compactDB = do
    n <- numVars `liftM` gets cnf
    lArr <- gets learnt
    clauses <- liftST $ (nub . Fl.concat) `liftM`
                        forM [L (- n) .. L n]
                           (\v -> do val <- readArray lArr v ; writeArray lArr v []
                                     return val)
    let clauses' = take (length clauses `div` 2)
                   $ sortBy (comparing (length . (\(_,s,_) -> s))) clauses
    liftST $ forM_ clauses'
             (\ wCl@(r, _, _) -> do
                (x, y) <- readSTRef r
                modifyArray lArr x $ const (wCl:)
                modifyArray lArr y $ const (wCl:))

-- *** Unit propagation

-- | Add clause to the watcher lists, unless clause is a singleton; if clause
-- is a singleton, `enqueue's fact and returns `False' if fact is in conflict,
-- `True' otherwise.  This function should be called exactly once per clause,
-- per run.  It should not be called to reconstruct the watcher list when
-- propagating.
--
-- Currently the watched literals in each clause are the first two.
--
-- Also adds unique clause ids to trace.
watchClause :: MAssignment s
            -> (Clause, ClauseId)
            -> Bool             -- ^ Is this clause learned?
            -> FunMonad s Bool
{-# INLINE watchClause #-}
watchClause m (c, cid) isLearnt = do
    case c of
      [] -> return True
      [l] -> do result <- enqueue m l (Just (c, cid))
                levelArr <- gets level
                liftST $ writeArray levelArr (var l) 0
                when (not isLearnt) (
                  modifySlot resolutionTrace $ \s rt ->
                      s{resolutionTrace=rt{resTraceOriginalSingles=
                                               (c,cid):resTraceOriginalSingles rt}})
                return result
      _ -> do let p = (negate (c !! 0), negate (c !! 1))
                  _insert annCl@(_, cl) list -- avoid watching dup clauses
                      | any (\(_, c) -> cl == c) list = list
                      | otherwise                     = annCl:list
              r <- liftST $ newSTRef p
              let annCl = (r, c, cid)
                  addCl arr = do modifyArray arr (fst p) $ const (annCl:)
                                 modifyArray arr (snd p) $ const (annCl:)
              get >>= liftST . addCl . (if isLearnt then learnt else watches)
              return True

-- | Enqueue literal in the `propQ' and place it in the current assignment.
-- If this conflicts with an existing assignment, returns @False@; otherwise
-- returns @True@.  In case there is a conflict, the assignment is /not/
-- altered.
--
-- Also records decision level, modifies trail, and records reason for
-- assignment.
enqueue :: MAssignment s
        -> Lit
           -- ^ The literal that has been assigned true.
        -> Maybe (Clause, ClauseId)
           -- ^ The reason for enqueuing the literal.  Including a
           -- non-@Nothing@ value here adjusts the `reason' map.
        -> FunMonad s Bool
{-# INLINE enqueue #-}
-- enqueue _m l _r | trace ("enqueue " ++ show l) $ False = undefined
enqueue m l r = do
    mFr <- unsafeFreezeAss m
    case l `statusUnder` mFr of
      Right b -> return b         -- conflict/already assigned
      Left () -> do
        liftST $ m `assign` l
        -- assign decision level for literal
        gets (level &&& (length . dl)) >>= \(levelArr, dlInt) ->
          liftST (writeArray levelArr (var l) dlInt)
        modify $ \s -> s{ trail = l : (trail s)
                        , propQ = propQ s Seq.|> l } 
        when (isJust r) $
          modifySlot reason $ \s m -> s{reason = Map.insert (var l) (fromJust r) m}
        return True

-- | Pop the `propQ'.  Error (crash) if it is empty.
dequeue :: FunMonad s Lit
{-# INLINE dequeue #-}
dequeue = do
    q <- gets propQ
    case Seq.viewl q of
      Seq.EmptyL -> error "dequeue of empty propQ"
      top Seq.:< q' -> do
        modify $ \s -> s{propQ = q'}
        return top

-- | Clear the `propQ'.
clearQueue :: FunMonad s ()
{-# INLINE clearQueue #-}
clearQueue = modify $ \s -> s{propQ = Seq.empty}

-- *** Dynamic variable ordering

-- | Modify priority of variable; takes care of @Double@ overflow.
varOrderMod :: Var -> (Double -> Double) -> FunMonad s ()
varOrderMod v f = do
    vo <- varOrderArr `liftM` gets varOrder
    vActivity <- liftST $ readArray vo v
    when (f vActivity > 1e100) $ rescaleActivities vo
    liftST $ writeArray vo v (f vActivity)
  where
    rescaleActivities vo = liftST $ do
        indices <- range `liftM` getBounds vo
        forM_ indices (\i -> modifyArray vo i $ const (* 1e-100))


-- | Retrieve the maximum-priority variable from the variable order.
varOrderGet :: IAssignment -> FrozenVarOrder -> Maybe Var
{-# INLINE varOrderGet #-}
varOrderGet mFr (FrozenVarOrder voFr) =
    -- find highest var undef under mFr, then find one with highest activity
    (`fmap` goUndef highestIndex) $ \start -> goActivity start start
  where
    highestIndex = snd . bounds $ voFr
    maxActivity v v' = if voFr!v > voFr!v' then v else v'

    -- @goActivity current highest@ returns highest-activity var
    goActivity !(V 0) !h   = h
    goActivity !v@(V n) !h = if v `isUndefUnder` mFr
                             then goActivity (V $! n-1) (v `maxActivity` h)
                             else goActivity (V $! n-1) h

    -- returns highest var that is undef under mFr
    goUndef !(V 0) = Nothing
    goUndef !v@(V n) | v `isUndefUnder` mFr = Just v
                     | otherwise            = goUndef (V $! n-1)


-- | Generate a new clause identifier (always unique).
nextTraceId :: FunMonad s Int
nextTraceId = do
    counter <- gets (resTraceIdCount . resolutionTrace)
    modifySlot resolutionTrace $ \s rt ->
        s{ resolutionTrace = rt{ resTraceIdCount = succ counter }}
    return $! counter

-- | Add the given clause id to the trace.
traceClauseId :: ClauseId -> FunMonad s ()
traceClauseId cid = do
    modifySlot resolutionTrace $ \s rt ->
        s{resolutionTrace = rt{ resTrace = [cid] }}


-- *** Generic state transition notation

-- | Guard a transition action.  If the boolean is true, return the action
-- given as an argument.  Otherwise, return `Nothing'.
(==>) :: (Monad m) => Bool -> m a -> Maybe (m a)
{-# INLINE (==>) #-}
(==>) b amb = guard b >> return amb

infixr 6 ==>

-- | @flip fmap@.
(>=>) :: (Monad m) => Maybe a -> (a -> m b) -> Maybe (m b)
{-# INLINE (>=>) #-}
(>=>) = flip fmap

infixr 6 >=>


-- | Choice of state transitions.  Choose the leftmost action that isn't
-- @Nothing@, or return @Nothing@ otherwise.
(><) :: (Monad m) => Maybe (m a) -> Maybe (m a) -> Maybe (m a)
a1 >< a2 =
    case (a1, a2) of
      (Nothing, Nothing) -> Nothing
      (Just _, _)        -> a1
      _                  -> a2

infixl 5 ><

-- *** Misc

initialActivity :: Double
initialActivity = 1.0

instance Error (Lit, Clause, ClauseId) where noMsg = (L 0, [], 0)
instance Error () where noMsg = ()


data VerifyError =
    SatError [(Clause, Either () Bool)]
      -- ^ Indicates a unsatisfactory assignment that was claimed
      -- satisfactory.  Each clause is tagged with its status using
      -- 'Funsat.Types.Model'@.statusUnder@.

    | UnsatError ResolutionError 
      -- ^ Indicates an error in the resultion checking process.

                   deriving (Show)

-- | Verify the solution.  In case of `Sat', checks that the assignment is
-- well-formed and satisfies the CNF problem.  In case of `Unsat', runs a
-- resolution-based checker on a trace of the SAT solver.
verify :: Solution -> Maybe ResolutionTrace -> CNF -> Maybe VerifyError
verify sol maybeRT cnf =
   -- m is well-formed
--    Fl.all (\l -> m!(V l) == l || m!(V l) == negate l || m!(V l) == 0) [1..numVars cnf]
    case sol of
      Sat m ->
          let unsatClauses = toList $
                             Set.filter (not . isTrue . snd) $
                             Set.map (\c -> (c, c `statusUnder` m)) (clauses cnf)
          in if null unsatClauses
             then Nothing
             else Just . SatError $ unsatClauses
      Unsat _ ->
          case Resolution.checkDepthFirst (fromJust maybeRT) of
            Left er -> Just . UnsatError $ er
            Right _ -> Nothing
  where isTrue (Right True) = True
        isTrue _            = False

---------------------------------------
-- Statistics & trace


data Stats = Stats
    { statsNumConfl :: Int64
      -- ^ Number of conflicts since last restart.

    , statsNumConflTotal :: Int64
      -- ^ Number of conflicts since beginning of solving.

    , statsNumLearnt :: Int64
      -- ^ Number of learned clauses currently in DB (fluctuates because DB is
      -- compacted every restart).

    , statsAvgLearntLen :: Double
      -- ^ Avg. number of literals per learnt clause.

    , statsNumDecisions :: Int64
      -- ^ Total number of decisions since beginning of solving.

    , statsNumImpl :: Int64
      -- ^ Total number of unit implications since beginning of solving.
    }

-- |  The show instance uses the wrapped string.
newtype ShowWrapped = WrapString { unwrapString :: String }
instance Show ShowWrapped where show = unwrapString

instance Show Stats where show = show . statTable

-- | Convert statistics to a nice-to-display tabular form.
statTable :: Stats -> Tabular.Table ShowWrapped
statTable s =
    Tabular.mkTable
                   [ [WrapString "Num. Conflicts"
                     ,WrapString $ show (statsNumConflTotal s)]
                   , [WrapString "Num. Learned Clauses"
                     ,WrapString $ show (statsNumLearnt s)]
                   , [WrapString " --> Avg. Lits/Clause"
                     ,WrapString $ show (statsAvgLearntLen s)]
                   , [WrapString "Num. Decisions"
                     ,WrapString $ show (statsNumDecisions s)]
                   , [WrapString "Num. Propagations"
                     ,WrapString $ show (statsNumImpl s)] ]

-- | Converts statistics into a tabular, human-readable summary.
statSummary :: Stats -> String
statSummary s =
     show (Tabular.mkTable
           [[WrapString $ show (statsNumConflTotal s) ++ " Conflicts"
            ,WrapString $ "| " ++ show (statsNumLearnt s) ++ " Learned Clauses"
                      ++ " (avg " ++ printf "%.2f" (statsAvgLearntLen s)
                      ++ " lits/clause)"]])


extractStats :: FunMonad s Stats
extractStats = do
  s <- gets stats
  learntArr <- get >>= liftST . unsafeFreezeWatchArray . learnt
  let learnts = (nub . Fl.concat)
        [ map (sort . (\(_,c,_) -> c)) (learntArr!i)
        | i <- (range . bounds) learntArr ] :: [Clause]
      stats =
        Stats { statsNumConfl = numConfl s
              , statsNumConflTotal = numConflTotal s
              , statsNumLearnt = fromIntegral $ length learnts
              , statsAvgLearntLen =
                fromIntegral (foldl' (+) 0 (map length learnts))
                / fromIntegral (statsNumLearnt stats)
              , statsNumDecisions = numDecisions s
              , statsNumImpl = numImpl s }
  return stats

unsafeFreezeWatchArray :: WatchArray s -> ST s (Array Lit [WatchedPair s])
unsafeFreezeWatchArray = freeze


constructResTrace :: Solution -> FunMonad s ResolutionTrace
constructResTrace sol = do
    s <- get
    watchesIndices <- range `liftM` liftST (getBounds (watches s))
    origClauseMap <-
        foldM (\origMap i -> do
                 clauses <- liftST $ readArray (watches s) i
                 return $
                   foldr (\(_, clause, clauseId) origMap ->
                           Map.insert clauseId clause origMap)
                         origMap
                         clauses)
              Map.empty
              watchesIndices
    let singleClauseMap =
            foldr (\(clause, clauseId) m -> Map.insert clauseId clause m)
                  Map.empty
                  (resTraceOriginalSingles . resolutionTrace $ s)
        anteMap =
            foldr (\l anteMap -> Map.insert (var l) (getAnteId s (var l)) anteMap)
                  Map.empty
                  (litAssignment . finalAssignment $ sol)
    return
      (initResolutionTrace
       (head (resTrace . resolutionTrace $ s))
       (finalAssignment sol))
      { traceSources = resSourceMap . resolutionTrace $ s
      , traceOriginalClauses = origClauseMap `Map.union` singleClauseMap
      , traceAntecedents = anteMap }
  where
    getAnteId s v = snd $
        Map.findWithDefault (error $ "no reason for assigned var " ++ show v)
        v (reason s)
