{-# LANGUAGE PatternSignatures
            ,MultiParamTypeClasses
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
reductions from many other interesting problems.  We hope this implementation
is efficient enough to make it useful to solve medium-size, real-world problem
mapped from another space.  We also aim to test the solver rigorously to
encourage confidence in its output.

One particular nicetie facilitating integration of Funsat into other projects
is the efficient calculation of an /unsatisfiable core/ for unsatisfiable
problems (see the "Funsat.Resolution" module).  In the case a problem is
unsatisfiable, as a by-product of checking the proof of unsatisfiability,
Funsat will generate a minimal set of input clauses that are also
unsatisfiable.

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
        , DPLLConfig(..)
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

    funsat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    funsat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with funsat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}


-- import Data.Graph.Inductive.Graphviz
import Control.Arrow ((&&&))
import Control.Exception (assert)
import Control.Monad.Error hiding ((>=>), forM_, runErrorT)
import Control.Monad.MonadST( MonadST(..) )
import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable hiding (sequence_)
import Data.Graph.Inductive.Graph( DynGraph, Graph )
import Data.Int (Int64)
import Data.List (intercalate, nub, tails, sortBy, intersect, sort)
import Data.Map (Map)
import Data.Maybe
import Data.Ord (comparing)
import Data.PSQueue( PSQ, Binding(..) )
import Data.STRef
import Data.Sequence (Seq)
import Data.Set (Set)
import Debug.Trace (trace)
import Funsat.Monad
import Funsat.Resolution( ResolutionError(..) )
import Funsat.Resolution( ResolutionTrace(..), initResolutionTrace )
import Funsat.Types
import Funsat.Utils
import Prelude hiding (sum, concatMap, elem, foldr, foldl, any, maximum)
import Text.Printf( printf )
import qualified Data.FRef as FRef
import qualified Data.Foldable as Fl
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Funsat.Resolution as Resolution
import qualified Data.PSQueue as PSQ
import qualified Text.Tabular as Tabular

-- * Interface

-- | Run the DPLL-based SAT solver on the given CNF instance.  Returns a
-- solution, along with internal solver statistics and possibly a resolution
-- trace.  The trace is for checking a proof of `Unsat', and thus is only
-- present then.
solve :: DPLLConfig -> CNF -> (Solution, Stats, Maybe ResolutionTrace)
solve cfg fIn =
    -- To solve, we simply take baby steps toward the solution using solveStep,
    -- starting with an initial assignment.
--     trace ("input " ++ show f) $
    either (error "no solution") id $
    runST $
    evalSSTErrMonad
        (do sol <- stepToSolution $ do
              initialAssignment <- liftST $ newSTUArray (V 1, V (numVars f)) 0
              (a, isUnsat) <- initialState initialAssignment
              if isUnsat then return (Right (Unsat a))
               else solveStep initialAssignment
            stats <- extractStats
            case sol of
              Sat _   -> return (sol, stats, Nothing)
              Unsat _ -> do resTrace <- constructResTrace sol
                            return (sol, stats, Just resTrace))
    SC{ cnf=f{clauses = Set.empty}, dl=[]
      , watches=undefined, learnt=undefined, propQ=Seq.empty
      , trail=[], numConfl=0, level=undefined, numConflTotal=0
      , numDecisions=0, numImpl=0
      , reason=Map.empty, varOrder=VarOrder PSQ.empty
      , resolutionTrace=PartialResolutionTrace 1 [] [] Map.empty
      , dpllConfig=cfg }
  where
    f = preprocessCNF fIn
    -- If returns True, then problem is unsat.
    initialState :: MAssignment s -> DPLLMonad s (IAssignment, Bool)
    initialState m = do
      initialLevel <- liftST $ newSTUArray (V 1, V (numVars f)) noLevel
      modify $ \s -> s{level = initialLevel}
      initialWatches <- liftST $ newSTArray (L (- (numVars f)), L (numVars f)) []
      modify $ \s -> s{ watches = initialWatches }
      initialLearnts <- liftST $ newSTArray (L (- (numVars f)), L (numVars f)) []
      modify $ \s -> s{ learnt = initialLearnts }
      modify $ \s -> s{ varOrder =
                            VarOrder . PSQ.fromAscList $ map (:-> initialActivity) [V 1 .. V (numVars f)] }

      (`catchError` (const $ liftST (unsafeFreezeAss m) >>= \a -> return (a,True))) $ do
        forM_ (clauses f)
          (\c -> do cid <- nextTraceId
                    isConsistent <- watchClause m (c, cid) False
                    when (not isConsistent)
                      -- conflict data is ignored here, so safe to fake
                      (do traceClauseId cid
                          throwError (L 0, [], 0)))
        a <- liftST (unsafeFreezeAss m)
        return (a, False)


-- | Solve with the default configuration `defaultConfig'.
solve1 :: CNF -> (Solution, Stats, Maybe ResolutionTrace)
solve1 f = solve (defaultConfig f) f

-- | Configuration parameters for the solver.
data DPLLConfig = Cfg
    { configRestart :: !Int64      -- ^ Number of conflicts before a restart.
    , configRestartBump :: !Double -- ^ `configRestart' is altered after each
                                   -- restart by multiplying it by this value.
    , configUseVSIDS :: !Bool      -- ^ If true, use dynamic variable ordering.
    , configUseRestarts :: !Bool }
                  deriving Show

-- | A default configuration based on the formula to solve.
--
--  * restarts every 100 conflicts
--
--  * requires 1.5 as many restarts after restarting as before, each time
--
--  * VSIDS to be enabled
--
--  * restarts to be enabled
defaultConfig :: CNF -> DPLLConfig
defaultConfig _f = Cfg { configRestart = 100 -- fromIntegral $ max (numVars f `div` 10) 100
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
simplifyDB :: IAssignment -> DPLLMonad s ()
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
solveStep :: MAssignment s -> DPLLMonad s (Step s)
solveStep m = do
    unsafeFreezeAss m >>= solveStepInvariants
    conf <- gets dpllConfig
    let selector = if configUseVSIDS conf then select else selectStatic
    maybeConfl <- bcp m
    mFr <- unsafeFreezeAss m
    s <- get
    newState $ 
          -- Check if unsat.
          unsat maybeConfl s ==> postProcessUnsat maybeConfl
          -- Unit propagation may reveal conflicts; check.
       >< maybeConfl         >=> backJump m
          -- No conflicts.  Decide.
       >< selector mFr (varOrder s)  >=> decide m
    where
      -- Take the step chosen by the transition guards above.
      newState stepMaybe =
         case stepMaybe of
           -- No step to do => satisfying assignment. (p. 6)
           Nothing   -> unsafeFreezeAss m >>= return . Right . Sat
           -- A step to do => do it, then see what it says.
           Just step -> do
                r <- step
                case r of
                  Nothing -> do a <- liftST (unsafeFreezeAss m)
                                return . Right . Unsat $ a
                  Just m  -> return . Left $ m
--                 liftM (maybe (Right Unsat) Left) 

-- | /Precondition:/ problem determined to be unsat.
--
-- Records id of conflicting clause in trace.
postProcessUnsat :: Maybe (Lit, Clause, ClauseId) -> DPLLMonad s (Maybe a)
postProcessUnsat maybeConfl = do
    traceClauseId $ (thd . fromJust) maybeConfl
    return Nothing
  where
    thd (_,_,i) = i

-- | Check data structure invariants.  Unless @-fno-ignore-asserts@ is passed,
-- this should be optimised away to nothing.
solveStepInvariants :: IAssignment -> DPLLMonad s ()
{-# INLINE solveStepInvariants #-}
solveStepInvariants _m = assert True $ do
  s <- get
  -- no dups in decision list or trail
  assert ((length . dl) s == (length . nub . dl) s) $
   assert ((length . trail) s == (length . nub . trail) s) $
   return ()


-- | A state transition, or /step/, produces either an intermediate assignment
-- (using `Left') or a solution to the instance.
type Step s = Either (MAssignment s) Solution
             
-- | The solution to a SAT problem is either an assignment or unsatisfiable.
data Solution = Sat IAssignment | Unsat IAssignment deriving (Eq)

finalAssignment :: Solution -> IAssignment
finalAssignment (Sat a)   = a
finalAssignment (Unsat a) = a

-- | This function applies `solveStep' recursively until SAT instance is
-- solved.  It also implements the conflict-based restarting (see
-- `DPLLConfig').
stepToSolution :: DPLLMonad s (Step s) -> DPLLMonad s Solution
stepToSolution stepAction = do
    step <- stepAction
    useRestarts <- gets (configUseRestarts . dpllConfig)
    restart <- uncurry ((>=)) `liftM`
               gets (numConfl &&& (configRestart . dpllConfig))
    case step of
      Left m -> do when (useRestarts && restart)
                     (do _stats <- extractStats
--                          trace ("Restarting...") $
--                           trace (statSummary stats) $
                         resetState m)
                   stepToSolution (solveStep m)
      Right s -> return s
  where
    resetState m = do
      modify $ \s -> s{ numConfl = 0 }
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

instance Show Solution where
   show (Sat a)     = "satisfiable: " ++ showAssignment a
   show (Unsat _)   = "unsatisfiable"


-- ** Internal data types

type Level = Int

-- | A /level array/ maintains a record of the decision level of each variable
-- in the solver.  If @level@ is such an array, then @level[i] == j@ means the
-- decision level for var number @i@ is @j@.  @j@ must be non-negative when
-- the level is defined, and `noLevel' otherwise.
--
-- Whenever an assignment of variable @v@ is made at decision level @i@,
-- @level[unVar v]@ is set to @i@.
type LevelArray s = STUArray s Var Level
-- | Immutable version.
type FrozenLevelArray = UArray Var Level

-- | Value of the `level' array if corresponding variable unassigned.  Had
-- better be less that 0.
noLevel :: Level
noLevel = -1

-- | The VSIDS-like dynamic variable ordering.
newtype VarOrder = VarOrder { varOrderPQ :: PSQ Var Double }
    deriving Show

-- | Each pair of watched literals is paired with its clause and id.
type WatchedPair s = (STRef s (Lit, Lit), Clause, ClauseId)
type WatchArray s = STArray s Lit [WatchedPair s]

data PartialResolutionTrace = PartialResolutionTrace
    { resTraceIdCount :: !Int
    , resTrace :: ![Int]
    , resTraceOriginalSingles :: ![(Clause, ClauseId)]
      -- Singleton clauses are not stored in the database, they are assigned.
      -- But we need to record their ids, so we put them here.
    , resSourceMap :: Map ClauseId [ClauseId] }
                            deriving (Show)

type ReasonMap = Map Var (Clause, ClauseId)
type ClauseId = Int

-- ** State and Phases

data FunsatState s = SC
    { cnf :: CNF                -- ^ The problem.
    , dl :: [Lit]
      -- ^ The decision level (last decided literal on front).

    , watches :: WatchArray s
      -- ^ Invariant: if @l@ maps to @((x, y), c)@, then @x == l || y == l@.

    , learnt :: WatchArray s
      -- ^ Same invariant as `watches', but only contains learned conflict
      -- clauses.

    , propQ :: Seq Lit
      -- ^ A FIFO queue of literals to propagate.  This should not be
      -- manipulated directly; see `enqueue' and `dequeue'.

    , level :: LevelArray s

    , trail :: [Lit]
      -- ^ Chronological trail of assignments, last-assignment-at-head.

    , reason :: ReasonMap
      -- ^ For each variable, the clause that (was unit and) implied its value.

    , numConfl :: !Int64
      -- ^ The number of conflicts that have occurred since the last restart.

    , numConflTotal :: !Int64
      -- ^ The total number of conflicts.

    , numDecisions :: !Int64
      -- ^ The total number of decisions.

    , numImpl :: !Int64
      -- ^ The total number of implications (propagations).

    , varOrder :: VarOrder

    , resolutionTrace :: PartialResolutionTrace

    , dpllConfig :: DPLLConfig
    }
                         deriving Show

instance Show (STRef s a) where
    show = const "<STRef>"
instance Show (STUArray s Var Int) where
    show = const "<STUArray Var Int>"
instance Show (STUArray s Var Double) where
    show = const "<STUArray Var Double>"
instance Show (STArray s a b) where
    show = const "<STArray>"

-- | Our star monad, the DPLL State monad.  We use @ST@ for mutable arrays and
-- references, when necessary.  Most of the state, however, is kept in
-- `FunsatState' and is not mutable.
type DPLLMonad s = SSTErrMonad (Lit, Clause, ClauseId) (FunsatState s) s


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
          -> DPLLMonad s (Maybe (Lit, Clause, ClauseId))
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
             modify $ \s -> s{ numImpl = numImpl s + 1 }
             alter (annCl:) l
             isConsistent <- enqueue m (negate q) (Just (c, cid))
             when (not isConsistent) $ do -- unit literal is conflicting
                alter (restClauses ++) l
                clearQueue
                throwError (negate q, c, cid)

-- | Boolean constraint propagation of all literals in `propQ'.  If a conflict
-- is found it is returned exactly as described for `bcpLit'.
bcp :: MAssignment s -> DPLLMonad s (Maybe (Lit, Clause, ClauseId))
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
select :: IAssignment -> VarOrder -> Maybe Var
{-# INLINE select #-}
select = varOrderGet

selectStatic :: IAssignment -> a -> Maybe Var
{-# INLINE selectStatic #-}
selectStatic m _ = find (`isUndefUnder` m) (range . bounds $ m)

-- | Assign given decision variable.  Records the current assignment before
-- deciding on the decision variable indexing the assignment.
decide :: MAssignment s -> Var -> DPLLMonad s (Maybe (MAssignment s))
decide m v = do
  let ld = L (unVar v)
  (SC{dl=dl}) <- get
--   trace ("decide " ++ show ld) $ return ()
  modify $ \s -> s{ dl = ld:dl
                  , numDecisions = numDecisions s + 1 }
  enqueue m ld Nothing
  return $ Just m



-- *** Backtracking

-- | Non-chronological backtracking.  The current returns the learned clause
-- implied by the first unique implication point cut of the conflict graph.
backJump :: MAssignment s
         -> (Lit, Clause, ClauseId)
            -- ^ @(l, c)@, where attempting to assign @l@ conflicted with
            -- clause @c@.
         -> DPLLMonad s (Maybe (MAssignment s))
backJump m c@(_, _conflict, _) = get >>= \(SC{dl=dl, reason=_reason}) -> do
    _theTrail <- gets trail
--     trace ("********** conflict = " ++ show c) $ return ()
--     trace ("trail = " ++ show _theTrail) $ return ()
--     trace ("dlits (" ++ show (length dl) ++ ") = " ++ show dl) $ return ()
--          ++ "reason: " ++ Map.showTree _reason
--           ) (
    modify $ \s -> s{ numConfl = numConfl s + 1
                    , numConflTotal = numConflTotal s + 1 }
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
        -> DPLLMonad s (Clause, ClauseId, Int)
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
                -> DPLLMonad s (Clause, ClauseId, Int)
    firstUIPBFS m nVars reasonMap =  do
      resolveSourcesR <- liftST $ newSTRef [] -- trace sources
      let addResolveSource clauseId =
              liftST $ modifySTRef resolveSourcesR (clauseId:)
      -- Literals we should process.
      seenArr  <- liftST $ newSTUArray (V 1, V nVars) False
      counterR <- liftST $ newSTRef 0 -- Number of unprocessed current-level
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
      FRef.modify fsResSourceMapRef $ Map.insert clauseId (reverse rsReversed)

fsResSourceMapRef :: FRef.FRef (FunsatState s) (Map ClauseId [ClauseId])
fsResSourceMapRef =
    FRef.ref resSourceMap (\m rt -> rt{ resSourceMap = m })
    `FRef.compose` FRef.ref resolutionTrace (\t s -> s{ resolutionTrace = t })

-- | Delete the assignment to last-assigned literal.  Undoes the trail, the
-- assignment, sets `noLevel', undoes reason.
--
-- Does /not/ touch `dl'.
undoOne :: MAssignment s -> DPLLMonad s ()
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
bump :: Var -> DPLLMonad s ()
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
compactDB :: DPLLMonad s ()
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
            -> DPLLMonad s Bool
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
                                             (c,cid): resTraceOriginalSingles rt}})
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
        -> DPLLMonad s Bool
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
dequeue :: DPLLMonad s Lit
{-# INLINE dequeue #-}
dequeue = do
  q <- gets propQ
  case Seq.viewl q of
    Seq.EmptyL -> error "dequeue of empty propQ"
    top Seq.:< q' -> do
      modify $ \s -> s{propQ = q'}
      return top

-- | Clear the `propQ'.
clearQueue :: DPLLMonad s ()
{-# INLINE clearQueue #-}
clearQueue = modify $ \s -> s{propQ = Seq.empty}

-- *** Dynamic variable ordering

-- | Modify priority of variable; takes care of @Double@ overflow.
varOrderMod :: Var -> (Double -> Double) -> DPLLMonad s ()
varOrderMod v f = do
    h <- varOrderPQ `liftM` gets varOrder
    let h' = case PSQ.lookup v h of
               Nothing -> h
               Just vActivity ->
                   if f vActivity > 1e100
                   then rescaleHeap v h
                   else PSQ.adjust f v h
    modify $ \s -> s{ varOrder = VarOrder h' }
            
  where
    rescaleHeap v = PSQ.fromAscList . map rescaleBinding . PSQ.toAscList
        where rescaleBinding (k :-> p)
                          | k == v    = k :-> f (p * 1e-100)
                          | otherwise = k :-> (p * 1e-100)


-- | Retrieve the maximum-priority variable from the variable order.
varOrderGet :: IAssignment -> VarOrder -> Maybe Var
{-# INLINE varOrderGet #-}
varOrderGet mFr vo = findUndefInPQ (varOrderPQ vo)
    where
      findUndefInPQ q =
          case PSQ.minView q of
            Just (v :-> activity, q') ->
                if v `isUndefUnder` mFr
                then Just v
                else findUndefInPQ q'
            Nothing -> error "varOrderGet: no decision var"


-- | Generate a new clause identifier (always unique).
nextTraceId :: DPLLMonad s Int
nextTraceId = do
    counter <- gets (resTraceIdCount . resolutionTrace)
    modifySlot resolutionTrace $ \s rt ->
        s{ resolutionTrace = rt{ resTraceIdCount = succ counter }}
    return $! counter

-- | Add the given clause id to the trace.
traceClauseId :: ClauseId -> DPLLMonad s ()
traceClauseId cid = do
    modifySlot resolutionTrace $ \s rt ->
        s{resolutionTrace = rt{ resTrace = [cid] }}


-- *** Generic state transition notation

-- | Guard a transition action.  If the boolean is true, return the action
-- given as an argument.  Otherwise, return `Nothing'.
(==>) :: (Monad m) => Bool -> m a -> Maybe (m a)
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



-- | The union of the reason side and the conflict side are all the nodes in
-- the `cutGraph' (excepting, perhaps, the nodes on the reason side at
-- decision level 0, which should never be present in a learned clause).
data Cut f gr a b =
    Cut { reasonSide :: f Graph.Node
        -- ^ The reason side contains at least the decision variables.
        , conflictSide :: f Graph.Node
        -- ^ The conflict side contains the conflicting literal.
        , cutUIP :: Graph.Node
        , cutGraph :: gr a b }
instance (Show (f Graph.Node), Show (gr a b)) => Show (Cut f gr a b) where
    show (Cut { conflictSide = c, cutUIP = uip }) =
        "Cut (uip=" ++ show uip ++ ", cSide=" ++ show c ++ ")"

-- | Generate a cut using the given UIP node.  The cut generated contains
-- exactly the (transitively) implied nodes starting with (but not including)
-- the UIP on the conflict side, with the rest of the nodes on the reason
-- side.
uipCut :: (Graph gr) =>
          [Lit]                 -- ^ decision literals
       -> FrozenLevelArray
       -> gr a b                -- ^ conflict graph
       -> Graph.Node            -- ^ unassigned, implied conflicting node
       -> Graph.Node            -- ^ a UIP in the conflict graph
       -> Cut Set gr a b
uipCut dlits levelArr conflGraph conflNode uip =
    Cut { reasonSide   = Set.filter (\i -> levelArr!(V $ abs i) > 0) $
                         allNodes Set.\\ impliedByUIP
        , conflictSide = impliedByUIP
        , cutUIP       = uip
        , cutGraph     = conflGraph }
    where
      -- Transitively implied, and not including the UIP.  
      impliedByUIP = Set.insert extraNode $
                     Set.fromList $ tail $ DFS.reachable uip conflGraph
      -- The UIP may not imply the assigned conflict variable which needs to
      -- be on the conflict side, unless it's a decision variable or the UIP
      -- itself.
      extraNode = if L (negate conflNode) `elem` dlits || negate conflNode == uip
                  then conflNode -- idempotent addition
                  else negate conflNode
      allNodes = Set.fromList $ Graph.nodes conflGraph


-- | Generate a learned clause from a cut of the graph.  Returns a pair of the
-- learned clause and the decision level to which to backtrack.
cutLearn :: (Graph gr, Foldable f) => IAssignment -> FrozenLevelArray
         -> Cut f gr a b -> (Clause, Int)
cutLearn a levelArr cut =
    ( clause
      -- The new decision level is the max level of all variables in the
      -- clause, excluding the uip (which is always at the current decision
      -- level).
    , maximum0 (map (levelArr!) . (`without` V (abs $ cutUIP cut)) . map var $ clause) )
  where
    -- The clause is composed of the variables on the reason side which have
    -- at least one successor on the conflict side.  The value of the variable
    -- is the negation of its value under the current assignment.
    clause =
        foldl' (\ls i ->
                    if any (`elem` conflictSide cut) (Graph.suc (cutGraph cut) i)
                    then L (negate $ a!(V $ abs i)):ls
                    else ls)
               [] (reasonSide cut)
    maximum0 [] = 0            -- maximum0 has 0 as its max for the empty list
    maximum0 xs = maximum xs


-- | Annotate each variable in the conflict graph with literal (indicating its
-- assignment) and decision level.  The only reason we make a new datatype for
-- this is for its `Show' instance.
data CGNodeAnnot = CGNA Lit Level
instance Show CGNodeAnnot where
    show (CGNA (L 0) _) = "lambda"
    show (CGNA l lev) = show l ++ " (" ++ show lev ++ ")"

-- | Creates the conflict graph, where each node is labeled by its literal and
-- level.
--
-- Useful for getting pretty graphviz output of a conflict.
mkConflGraph :: DynGraph gr =>
                IAssignment
             -> FrozenLevelArray
             -> Map Var Clause
             -> [Lit]           -- ^ decision lits, in rev. chron. order
             -> (Lit, Clause)   -- ^ conflict info
             -> gr CGNodeAnnot ()
mkConflGraph mFr lev reasonMap _dlits (cLit, confl) =
    Graph.mkGraph nodes' edges'
  where
    -- we pick out all the variables from the conflict graph, specially adding
    -- both literals of the conflict variable, so that that variable has two
    -- nodes in the graph.
    nodes' =
            ((0, CGNA (L 0) (-1)) :) $ -- lambda node
            ((unLit cLit, CGNA cLit (-1)) :) $
            ((negate (unLit cLit), CGNA (negate cLit) (lev!(var cLit))) :) $
            -- annotate each node with its literal and level
            map (\v -> (unVar v, CGNA (varToLit v) (lev!v))) $
            filter (\v -> v /= var cLit) $
            toList nodeSet'
          
    -- node set includes all variables reachable from conflict.  This node set
    -- construction needs a `seen' set because it might infinite loop
    -- otherwise.
    (nodeSet', edges') =
        mkGr Set.empty (Set.empty, [ (unLit cLit, 0, ())
                                   , ((negate . unLit) cLit, 0, ()) ])
                       [negate cLit, cLit]
    varToLit v = (if v `isTrueUnder` mFr then id else negate) $ L (unVar v)

    -- seed with both conflicting literals
    mkGr _ ne [] = ne
    mkGr (seen :: Set Graph.Node) ne@(nodes, edges) (lit:lits) =
        if haveSeen
        then mkGr seen ne lits
        else newNodes `seq` newEdges `seq`
             mkGr seen' (newNodes, newEdges) (lits ++ pred)
      where
        haveSeen = seen `contains` litNode lit
        newNodes = var lit `Set.insert` nodes
        newEdges = [ ( litNode (negate x) -- unimplied lits from reasons are
                                          -- complemented
                     , litNode lit, () )
                     | x <- pred ] ++ edges
        pred = filterReason $
               if lit == cLit then confl else
               Map.findWithDefault [] (var lit) reasonMap `without` lit
        filterReason = filter ( ((var lit /=) . var) .&&.
                                ((<= litLevel lit) . litLevel) )
        seen' = seen `with` litNode lit
        litLevel l = if l == cLit then length _dlits else lev!(var l)
        litNode l =              -- lit to node
            if var l == var cLit -- preserve sign of conflicting lit
            then unLit l
            else (abs . unLit) l

showAssignment a = intercalate " " ([show (a!i) | i <- range . bounds $ a,
                                                  (a!i) /= 0])

initialActivity :: Double
initialActivity = 1.0

instance Error (Lit, Clause, ClauseId) where
    noMsg = (L 0, [], 0)

instance Error () where
    noMsg = ()


data VerifyError = SatError [(Clause, Either () Bool)]
                   -- ^ Indicates a unsatisfactory assignment that was claimed
                   -- satisfactory.  Each clause is tagged with its status
                   -- using 'Funsat.Types.Model'@.statusUnder@.

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
      Unsat m ->
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
instance Show ShowWrapped where
    show = unwrapString

instance Show Stats where
    show = show . statTable

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


extractStats :: DPLLMonad s Stats
extractStats = do
  s <- get
  learntArr <- liftST $ unsafeFreezeWatchArray (learnt s)
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


constructResTrace :: Solution -> DPLLMonad s ResolutionTrace
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
