{-# LANGUAGE PatternSignatures
            ,MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
            ,FlexibleContexts
            ,GeneralizedNewtypeDeriving
            ,TypeSynonymInstances
            ,TypeOperators
            ,ParallelListComp #-}
{-# OPTIONS -cpp #-}






{-|

Goal: A reasonably efficient, easy-to-understand modern sat solver.  I
want it to be as close as possible to the description of a basic, modern
solver from /Abstract DPLL and Abstract DPLL Modulo Theories/, while retaining
some efficient optimisations.

            Current state: decision heuristic/code cleanup/tests.

* 15 Dec 2007 22:46:11

backJump appears to work now.  I used to have both Just and Nothing cases
there, but there was no reason why, since either you always reverse some past
decision (maybe the most recent one).  Well, the problem had to do with
DecisionMap.  Basically instead of keeping around the implications of a
decision literal (those as a result of unit propagation *and* reversed
decisions of higher decision levels), I was throwing them away.  This was bad
for backJump.

Anyway, now it appears to work properly.

* 08 Dec 2007 22:15:44

IT IS ALIVE

I do need the /bad/ variables to be kept around, but I should only update the
list after I'm forced to backtrack *all the way to decision level 0*.  Only
then is a variable bad.  The Chaff paper makes you think you mark it as /tried
both ways/ the *first* time you see that, no matter the decision level.

On the other hand, why do I need a bad variable list at all?  The DPLL paper
doesn't imply that I should.  Hmm.

* 08 Dec 2007 20:16:17

For some reason, the /unsat/ (or /fail/ condition, in the DPLL paper) was not
sufficient: I was trying out all possible assignments but in the end I didn't
get a conflict, just no more options.  So I added an or to test for that case
in `unsat'.  Still getting assignments under which some clauses are undefined;
though, it appears they can always be extended to proper, satisfying
assignments.  But why does it stop before then?

* 20 Nov 2007 14:52:51

Any time I've spent coding on this I've spent trying to figure out why some
inputs cause divergence.  I finally figured out how (easily) to print out the
assignment after each step, and indeed the same decisions were being made
over, and over, and over again.  So I decided to keep a /bad/ list of literals
which have been tried both ways, without success, so that decLit never decides
based on one of those literals.  Now it terminates, but the models are (at
least) non-total, and (possibly) simply incorrect.  This leads me to believ
that either (1) the DPLL paper is wrong about not having to keep track of
whether you've tried a particular variable both ways, or (2) I misread the
paper or (3) I implemented incorrectly what is in the paper.  Hopefully before
I die I will know which of the three is the case.

* 17 Nov 2007 11:58:59:

Profiling reveals instance Model Lit Assignment accounts for 74% of time, and
instance Model Lit Clause Assignment accounts for 12% of time.  These occur in
the call graph under unitPropLit.  So clearly I need a *better way of
searching for the next unit literal*.

* Bibliography

''Abstract DPLL and DPLL Modulo Theories''

''Chaff: Engineering an Efficient SAT solver''

''An Extensible SAT-solver'' by Niklas Een, Niklas Sorensson

''Efficient Conflict Driven Learning in a Boolean Satisfiability Solver'' by
Zhang, Madigan, Moskewicz, Malik

''SAT-MICRO: petit mais costaud!'' by Conchon, Kanig, and Lescuyer

-}
module DPLLSat
#ifndef TESTING
        ( solve
        , solve1
        , DPLLConfig(..)
        , Solution(..)
        , CNF
        , GenCNF(..)
        , verify
        )
#endif
    where

{-
    This file is part of DPLLSat.

    DPLLSat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    DPLLSat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with DPLLSat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}


import Control.Arrow ((&&&))
import Control.Exception (assert)
import Control.Monad.Error hiding ((>=>), forM_)
import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Data.Array.ST
import Data.Array.Unboxed
import Data.BitSet (BitSet)
import Data.Foldable hiding (sequence_)
import Data.Graph.Inductive.Tree( Gr )
import Data.Graph.Inductive.Graph( DynGraph, Graph )
import Data.Graph.Inductive.Graphviz
import Data.Int (Int64)
import Data.List (intercalate, nub, tails, sortBy, intersect, foldl1', (\\), sort)
import Data.Map (Map)
import Data.Maybe
import Data.Ord (comparing)
import Data.STRef
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Tree
import Debug.Trace (trace)
import Prelude hiding (sum, concatMap, elem, foldr, foldl, any, maximum)
import System.Random
import System.IO.Unsafe (unsafePerformIO)
import System.IO (hPutStr, stderr)
import Text.Printf( printf )
import qualified Data.BitSet as BitSet
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.BFS as BFS
import qualified Data.Graph.Inductive.Query.SP as SP
import qualified Data.Foldable as Fl
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set


-- * Interface

-- | Run the DPLL-based SAT solver on the given CNF instance.
solve :: DPLLConfig -> StdGen -> CNF -> Solution
solve cfg g fIn =
    -- To solve, we simply take baby steps toward the solution using solveStep,
    -- starting with an initial assignment.
#ifdef TRACE
    trace ("input " ++ show f) $
#endif
    runST $
    evalStateT (stepToSolution $ do
                  initialAssignment <- lift $ newSTUArray (V 1, V (numVars f)) 0
                  isUnsat <- initialState initialAssignment
                  if isUnsat then return (Right Unsat)
                   else solveStep initialAssignment)
    SC{ cnf=f, dl=[], rnd=g
      , watches=undefined, learnt=undefined, propQ=Seq.empty
      , trail=[], numConfl=0, level=undefined
      , reason=Map.empty, varOrder=undefined
      , dpllConfig=cfg }
  where
    f = preprocessCNF fIn
    -- If returns True, then problem is unsat.
    initialState :: MAssignment s -> DPLLMonad s Bool
    initialState m = do
      f <- gets cnf
      initialLevel <- lift $ newSTUArray (V 1, V (numVars f)) noLevel
      modify $ \s -> s{level = initialLevel}
      initialWatches <- lift $ newSTArray (L (- (numVars f)), L (numVars f)) []
      modify $ \s -> s{ watches = initialWatches }
      initialLearnts <- lift $ newSTArray (L (- (numVars f)), L (numVars f)) []
      modify $ \s -> s{ learnt = initialLearnts }
      initialVarOrder <- lift $ newSTUArray (V 1, V (numVars f)) initialActivity
      modify $ \s -> s{ varOrder = VarOrder initialVarOrder }

      leftUnsat <-
        runErrorT $
        forM_ (clauses f)
          (\c -> do isConsistent <- lift $ watchClause m c False
                    when (not isConsistent) (throwError ()))
      return (either (const True) (const False) leftUnsat)


-- | Solve with a constant random seed and default configuration
-- `defaultConfig' (for debugging).
solve1 :: CNF -> Solution
solve1 f = solve (defaultConfig f) (mkStdGen 1) f

-- | Configuration parameters for the solver.
data DPLLConfig = Cfg
    { configRestart :: Int64      -- ^ Number of conflicts before a restart.
    , configRestartBump :: Double -- ^ `configRestart' is altered after each
                                  -- restart by multiplying it by this value.
    }
                  deriving Show

-- | A default configuration based on the formula to solve.
defaultConfig :: CNF -> DPLLConfig
defaultConfig _f = Cfg { configRestart = 100
                      , configRestartBump = 1.5 }

-- * Preprocessing

-- | Some kind of preprocessing.
--
--   * remove duplicates
preprocessCNF :: CNF -> CNF
preprocessCNF f = f{clauses = simpClauses (clauses f)}
    where simpClauses = Set.map nub -- rm dups

-- | Simplify the clause database.  Eventually should supersede, probably,
-- `preprocessCNF'.
simplifyDB :: IAssignment -> DPLLMonad s ()
simplifyDB _mFr = undefined

-- * Internals

-- | The DPLL procedure is modeled as a state transition system.  This
-- function takes one step in that transition system.  Given an unsatisfactory
-- assignment, perform one state transition, producing a new assignment and a
-- new state.
solveStep :: MAssignment s -> DPLLMonad s (Step s)
solveStep m = do
    maybeConfl <- bcp m
    mFr <- lift $ unsafeFreezeAss m
    s <- get
    voFr <- FrozenVarOrder `liftM` lift (unsafeFreeze . varOrderArr . varOrder $ s)
    newState $ 
          -- Check if unsat.
          unsat maybeConfl s      ==> return Nothing
          -- Unit propagation may reveal conflicts; check.
       >< maybeConfl              >=> backJump m
          -- No conflicts.  Decide.
       >< select mFr voFr >=> decide m
    where
      -- Take the step chosen by the transition guards above.
      newState stepMaybe =
         case stepMaybe of
           -- No step to do => satisfying assignment. (p. 6)
           Nothing   -> lift (unsafeFreezeAss m) >>= return . Right . Sat
           -- A step to do => do it, then see what it says.
           Just step -> step >>= return . maybe (Right Unsat) Left


-- | A state transition, or /step/, produces either an intermediate assignment
-- (using `Left') or a solution to the instance.
type Step s = Either (MAssignment s) Solution
             
-- | The solution to a SAT problem is either an assignment or unsatisfiable.
data Solution = Sat IAssignment | Unsat deriving (Eq)

-- | This function applies `solveStep' recursively until SAT instance is
-- solved.  It also implements the conflict-based restarting (see
-- `DPLLConfig').
stepToSolution :: DPLLMonad s (Step s) -> DPLLMonad s Solution
stepToSolution stepAction = do
    step <- stepAction
    restart <- uncurry ((>=)) `liftM`
               gets (numConfl &&& (configRestart . dpllConfig))
    case step of
      Left m -> do when restart
                     (do stats <- extractStats
                         trace (show stats) $
                          resetState m)
                   stepToSolution (solveStep m)
      Right s -> return s
  where
    resetState m = do
      -- Require more conflicts before next restart.
      modifySlot dpllConfig $ \s c ->
        s{ dpllConfig = c{ configRestart = ceiling (configRestartBump c
                                                   * fromIntegral (configRestart c))
                           } }
      lvl :: FrozenLevelArray <- gets level >>= lift . unsafeFreeze
      undoneLits <- takeWhile (\l -> lvl ! (var l) > 0) `liftM` gets trail
      forM_ undoneLits $ const (undoOne m)
      compact

{-# INLINE mytrace #-}
mytrace msg expr = unsafePerformIO $ do
    hPutStr stderr msg
    return expr

instance Show Solution where
   show (Sat a) = "satisfiable: " ++ showAssignment a
   show Unsat   = "unsatisfiable"


-- ** Star Data Types

newtype Var = V {unVar :: Int} deriving (Eq, Ord, Enum, Ix)

instance Show Var where
    show (V i) = show i ++ "v"

instance Num Var where
    _ + _ = error "+ doesn't make sense for variables"
    _ - _ = error "- doesn't make sense for variables"
    _ * _ = error "* doesn't make sense for variables"
    signum _ = error "signum doesn't make sense for variables"
    negate = error "negate doesn't make sense for variables"
    abs = id
    fromInteger l | l <= 0    = error $ show l ++ " is not a variable"
                  | otherwise = V $ fromInteger l

newtype Lit = L {unLit :: Int} deriving (Eq, Ord, Enum, Ix)
inLit f = L . f . unLit

instance Show Lit where
    show l = show ul
        where ul = unLit l
instance Read Lit where
    readsPrec i s = map (\(i,s) -> (L i, s)) (readsPrec i s :: [(Int, String)])

-- | The variable for the given literal.
var :: Lit -> Var
var = V . abs . unLit

instance Num Lit where
    _ + _ = error "+ doesn't make sense for literals"
    _ - _ = error "- doesn't make sense for literals"
    _ * _ = error "* doesn't make sense for literals"
    signum _ = error "signum doesn't make sense for literals"
    negate   = inLit negate
    abs      = inLit abs
    fromInteger l | l == 0    = error "0 is not a literal"
                  | otherwise = L $ fromInteger l

type Clause = [Lit]

-- | ''Generic'' conjunctive normal form.  It's ''generic'' because the
-- elements of the clause set are polymorphic.  And they are polymorphic so
-- that I can get a `Foldable' instance.
data GenCNF a = CNF {
      numVars :: Int,
      numClauses :: Int,
      clauses :: Set a
    }
                deriving (Show, Read, Eq)

type CNF = GenCNF Clause

instance Foldable GenCNF where
    -- TODO it might be easy to make this instance more efficient.
    foldMap toM cnf = foldMap toM (clauses cnf)


-- | There are a bunch of things in the state which are essentially used as
-- ''set-like'' objects.  I've distilled their interface into three methods.
-- These methods are used extensively in the implementation of the solver.
class Ord a => Setlike t a where
    -- | The set-like object with an element removed.
    without  :: t -> a -> t
    -- | The set-like object with an element included.
    with     :: t -> a -> t
    -- | Whether the set-like object contains a certain element.
    contains :: t -> a -> Bool

instance Ord a => Setlike (Set a) a where
    without  = flip Set.delete
    with     = flip Set.insert
    contains = flip Set.member

instance Ord a => Setlike [a] a where
    without  = flip List.delete
    with     = flip (:)
    contains = flip List.elem

instance Setlike IAssignment Lit where
    without a l  = a // [(var l, 0)]
    with a l     = a // [(var l, unLit l)]
    contains a l = unLit l == a ! (var l)

instance (Ord k, Ord a) => Setlike (Map k a) (k, a) where
    with m (k,v)    = Map.insert k v m
    without m (k,_) = Map.delete k m
    contains = error "no contains for Setlike (Map k a) (k, a)"

instance (Ord a, BitSet.Hash a) => Setlike (BitSet a) a where
    with = flip BitSet.insert
    without = flip BitSet.delete
    contains = flip BitSet.member


instance (BitSet.Hash Lit) where
    hash l = if li > 0 then 2 * vi else (2 * vi) + 1
        where li = unLit l
              vi = abs li

instance (BitSet.Hash Var) where
    hash = unVar


-- | An ''immutable assignmant''.  Stores the current assignment according to
-- the following convention.  A literal @L i@ is in the assignment if in
-- location @(abs i)@ in the array, @i@ is present.  Literal @L i@ is absent
-- if in location @(abs i)@ there is 0.  It is an error if the location @(abs
-- i)@ is any value other than @0@ or @i@ or @negate i@.
--
-- Note that the `Model' instance for `Lit' and `IAssignment' takes constant
-- time to execute because of this representation for assignments.  Also
-- updating an assignment with newly-assigned literals takes constant time,
-- and can be done destructively, but safely.
type IAssignment = UArray Var Int

-- | Mutable array corresponding to the `IAssignment' representation.
type MAssignment s = STUArray s Var Int

-- | Same as @freeze@, but at the right type so GHC doesn't yell at me.
freezeAss :: MAssignment s -> ST s IAssignment
freezeAss = freeze
-- | See `freezeAss'.
unsafeFreezeAss :: MAssignment s -> ST s IAssignment
unsafeFreezeAss = unsafeFreeze

thawAss :: IAssignment -> ST s (MAssignment s)
thawAss = thaw
unsafeThawAss :: IAssignment -> ST s (MAssignment s)
unsafeThawAss = unsafeThaw

-- | Destructively update the assignment with the given literal.
assign :: MAssignment s -> Lit -> ST s (MAssignment s)
assign a l = writeArray a (var l) (unLit l) >> return a

-- | Destructively undo the assignment to the given literal.
unassign :: MAssignment s -> Lit -> ST s (MAssignment s)
unassign a l = writeArray a (var l) 0 >> return a


-- | An instance of this class is able to answer the question, Is a
-- truth-functional object @x@ true under the model @m@?  Or is @m@ a model
-- for @x@?  There are three possible answers for this question: `True' (''the
-- object is true under @m@''), `False' (''the object is false under @m@''),
-- and undefined, meaning its status is uncertain or unknown (as is the case
-- with a partial assignment).
--
-- The only method in this class is so named so it reads well when used infix.
-- Also see: `isTrueUnder', `isFalseUnder', `isUndefUnder'.
class Model a m where
    -- | @x ``statusUnder`` m@ should use @Right@ if the status of @x@ is
    -- defined, and @Left@ otherwise.
    statusUnder :: a -> m -> Either () Bool

-- /O(1)/.
instance Model Lit IAssignment where
    statusUnder l a | a `contains` l        = Right True
                    | a `contains` negate l = Right False
                    | otherwise             = Left ()
instance Model Var IAssignment where
    statusUnder v a | a `contains` pos = Right True
                    | a `contains` neg = Right False
                    | otherwise        = Left ()
                    where pos = L (unVar v)
                          neg = negate pos
instance Model Clause IAssignment where
    statusUnder c m
        -- true if c intersect m is not null == a member of c in m
        | Fl.any (\e -> m `contains` e) c   = Right True
        -- false if all its literals are false under m.
        | Fl.all (`isFalseUnder` m) c = Right False
        | otherwise                = Left ()



-- | `True' if and only if the object is undefined in the model.
isUndefUnder :: Model a m => a -> m -> Bool
isUndefUnder x m = isUndef $ x `statusUnder` m
    where isUndef (Left ()) = True
          isUndef _         = False

-- | `True' if and only if the object is true in the model.
isTrueUnder :: Model a m => a -> m -> Bool
isTrueUnder x m = isTrue $ x `statusUnder` m
    where isTrue (Right True) = True
          isTrue _            = False

-- | `True' if and only if the object is false in the model.
isFalseUnder :: Model a m => a -> m -> Bool
isFalseUnder x m = isFalse $ x `statusUnder` m
    where isFalse (Right False) = True
          isFalse _             = False

isUnitUnder c m = isSingle (filter (not . (`isFalseUnder` m)) c)
                  && not (Fl.any (`isTrueUnder` m) c)

-- Precondition: clause is unit.
getUnit :: (Model a m) => [a] -> m -> a
getUnit c m = case filter (not . (`isFalseUnder` m)) c of
                [u] -> u
                _   -> error "getUnit: not unit"

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
newtype VarOrder s = VarOrder { varOrderArr :: STUArray s Var Double }
    deriving Show
newtype FrozenVarOrder = FrozenVarOrder (UArray Var Double)
    deriving Show

-- | Each pair of watched literals is paired with its clause.
type WatchedPair s = (STRef s (Lit, Lit), Clause)
type WatchArray s = STArray s Lit [WatchedPair s]

-- ** DPLL State and Phases

data DPLLStateContents s = SC
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
    , reason :: Map Var Clause
      -- ^ For each variable, the clause that (was unit and) implied its value.
    , numConfl :: Int64
      -- ^ The number of conflicts that have occurred since the last restart.
    , varOrder :: VarOrder s
    , rnd :: StdGen              -- ^ random source
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
-- `DPLLStateContents' and is not mutable.
type DPLLMonad s = StateT (DPLLStateContents s) (ST s)


-- *** Boolean constraint propagation

type ConflictMonad s = ErrorT (Lit, Clause) (DPLLMonad s)

-- | Assign a new literal, and enqueue any implied assignments.  If a conflict
-- is detected, return @Just (impliedLit, conflictingClause)@; otherwise
-- return @Nothing@.  The @impliedLit@ is implied by the clause, but conflicts
-- with the assignment.
--
-- If no new clauses are unit (i.e. no implied assignments), simply update
-- watched literals.
bcpLit :: MAssignment s
          -> Lit                -- ^ Assigned literal which might propagate.
          -> DPLLMonad s (Maybe (Lit, Clause))
bcpLit m l = do
    ws <- gets watches ; ls <- gets learnt
    clauses <- lift $ readArray ws l
    learnts <- lift $ readArray ls l
    lift $ do writeArray ws l [] ; writeArray ls l []

    -- Update wather lists for normal & learnt clauses; if conflict is found,
    -- return that and don't update anything else.
    c <- runErrorT $ do
           {-# SCC "bcpWatches" #-} forM_ (tails clauses) (updateWatches
             (\ f l -> lift . lift $ modifyArray ws l (const f)))
           {-# SCC "bcpLearnts" #-} forM_ (tails learnts) (updateWatches
             (\ f l -> lift . lift $ modifyArray ls l (const f)))
    case c of
      Left conflict -> return $ Just conflict
      Right _       -> return Nothing
  where
    -- updateWatches: `l' has been assigned, so we look at the clauses in
    -- which contain @negate l@, namely the watcher list for l.  For each
    -- annotated clause, find the status of its watched literals.  If a
    -- conflict is found, the at-fault clause is returned through Left, and
    -- the unprocessed clauses are placed back into the appropriate watcher
    -- list.
    {-# INLINE updateWatches #-}
    updateWatches _ [] = return ()
    updateWatches alter (annCl@(watchRef, c) : restClauses) = do
      mFr <- lift . lift $ unsafeFreezeAss m
      q   <- lift . lift $ do (x, y) <- readSTRef watchRef
                              return $ if x == l then y else x
      -- l,q are the (negated) literals being watched for clause c.
      if negate q `isTrueUnder` mFr -- if other true, clause already sat
       then alter (annCl:) l
       else
         case find (\x -> x /= negate q && x /= negate l
                          && not (x `isFalseUnder` mFr)) c of
           Just l' -> do     -- found unassigned literal, negate l', to watch
             lift . lift $ writeSTRef watchRef (q, negate l')
             alter (annCl:) (negate l')

           Nothing -> do      -- all other lits false, clause is unit
             alter (annCl:) l
             isConsistent <- lift $ enqueue m (negate q) (Just c)
             when (not isConsistent) $ do -- unit literal is conflicting
                alter (restClauses ++) l
                lift clearQueue
                throwError (negate q, c)

-- | Boolean constraint propagation of all literals in `propQ'.  If a conflict
-- is found it is returned exactly as described for `bcpLit'.
bcp :: MAssignment s -> DPLLMonad s (Maybe (Lit, Clause))
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
select = varOrderGet

-- | Assign given decision variable.  Records the current assignment before
-- deciding on the decision variable indexing the assignment.
decide :: MAssignment s -> Var -> DPLLMonad s (Maybe (MAssignment s))
decide m v = do
  let ld = L (unVar v)
  (SC{dl=dl}) <- get
--   trace ("decide " ++ show ld) $
  modify $ \s -> s{ dl = ld:dl }
  enqueue m ld Nothing
  return $ Just m



-- *** Backtracking

-- | Non-chronological backtracking.  The current returns the learned clause
-- implied by the first unique implication point cut of the conflict graph.
backJump :: MAssignment s
         -> (Lit, Clause)
            -- ^ @(l, c)@, where attempting to assign @l@ conflicted with
            -- clause @c@.
         -> DPLLMonad s (Maybe (MAssignment s))
backJump m c@(_, conflict) = get >>= \(SC{dl=dl, reason=_reason}) -> do
    _theTrail <- gets trail
--     trace ("********** conflict = " ++ show c ++ "\n"
--           ++ "trail = " ++ show theTrail ++ "\n"
--           ++ "dlits = " ++ show dl ++ "\n"
--          ++ "reason: " ++ Map.showTree reason
--           ) (
    modify $ \s -> s{numConfl = numConfl s + 1}
    levelArr :: FrozenLevelArray <- do s <- get
                                       lift $ unsafeFreeze (level s)
    (learntCl, newLevel) <-
        do mFr <- lift $ unsafeFreezeAss m
           analyse mFr levelArr dl c
    s <- get
    let numDecisionsToUndo = length dl - newLevel
        dl' = drop numDecisionsToUndo dl
        undoneLits = takeWhile (\lit -> levelArr ! (var lit) > newLevel) (trail s) 
    forM_ undoneLits $ const (undoOne m) -- backtrack
    mFr <- lift $ unsafeFreezeAss m
    assert (numDecisionsToUndo > 0) $
     assert (not (null learntCl)) $
     assert (learntCl `isUnitUnder` mFr) $
     modify $ \s -> s{ dl  = dl' } -- undo decisions
    forM_ conflict (bump . var)
    enqueue m (getUnit learntCl mFr) (Just learntCl) -- learntCl is asserting
    _mFr <- lift $ unsafeFreezeAss m
--     trace ("new mFr: " ++ showAssignment _mFr) $ return ()
    watchClause m learntCl True
    return $ Just m

-- | Analyse a the conflict graph and produce a learned clause.  We use the
-- First UIP cut of the conflict graph.
analyse :: IAssignment -> FrozenLevelArray -> [Lit] -> (Lit, Clause)
        -> DPLLMonad s (Clause, Int) -- ^ learned clause and new decision level
analyse mFr levelArr dlits c@(cLit, _cClause) = do
    st <- get
--     trace ("mFr: " ++ showAssignment mFr) $ assert True (return ())
    let (learntCl, newLevel) = cutLearn mFr levelArr firstUIPCut
        firstUIPCut = uipCut dlits levelArr conflGraph (unLit cLit)
                      (firstUIP conflGraph)
        conflGraph = mkConflGraph mFr levelArr (reason st) dlits c
                     :: Gr CGNodeAnnot Int
--     outputConflict (graphviz' conflGraph) $
--     trace ("graphviz graph:\n" ++ graphviz' conflGraph) $
--     trace ("cut: " ++ show firstUIPCut) $
--     trace ("learnt: " ++ show (learntCl, newLevel)) $
    return $ (learntCl, newLevel)
  where
    firstUIP conflGraph = -- trace ("--> uips = " ++ show uips) $
--                           trace ("--> dom " ++ show conflNode
--                                  ++ " = " ++ show domConfl) $
--                           trace ("--> dom " ++ show (negate conflNode)
--                                  ++ " = " ++ show domAssigned) $
                          argminimum distanceFromConfl uips :: Graph.Node
        where
          uips        = domConfl `intersect` domAssigned :: [Graph.Node]
          -- `domConfl' never gives us vacuous dominators since there is by
          -- construction a path on the current decision level to the implied,
          -- conflicting node.  OTOH, there might be no path from dec. var. to
          -- the assigned literal which is conflicting (negate conflNode).
          domConfl    = filter (\i -> levelN i == currentLevel && i /= conflNode) $
                        fromJust $ lookup conflNode domFromLastd
          domAssigned =
              -- if assigned conflict node is not implied by the current-level
              -- dec var, then the only dominator we should list of it should
              -- be the dec var.
              if negate conflNode `elem` BFS.bfs (abs $ unLit lastd) conflGraph
              then 
                  filter (\i -> levelN i == currentLevel && i /= conflNode) $
                  fromJust $ lookup (negate conflNode) domFromLastd
              else [(abs $ unLit lastd)]
          domFromLastd = dom conflGraph (abs $ unLit lastd)
          distanceFromConfl x = SP.spLength x conflNode conflGraph :: Int

    -- helpers
    lastd        = head dlits
    conflNode    = unLit cLit
    currentLevel = length dlits
    levelN i = if i == unLit cLit then currentLevel else ((levelArr!) . V . abs) i
    outputConflict g x = unsafePerformIO $ do writeFile "conflict.dot" g
                                              return x

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
        "Cut (c=" ++ show c ++ ", uip=" ++ show uip ++ ")"

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
    Cut { reasonSide   = Set.filter (\i -> levelArr!(V i) > 0) $
                         allNodes Set.\\ impliedByUIP
        , conflictSide = impliedByUIP
        , cutUIP       = uip
        , cutGraph     = conflGraph }
    where
      -- The UIP may not imply the assigned conflict variable, so add it
      -- manually, unless it's a decision variable.
      extraNode = if L (negate conflNode) `elem` dlits
                  then conflNode -- idempotent addition
                  else negate conflNode
      -- Transitively implied, and not including the UIP.  
      impliedByUIP = Set.insert extraNode $
                     Set.fromList $ tail $ BFS.bfs uip conflGraph
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
    , maximum0 (map (levelArr!) . (`without` V (cutUIP cut)) . map var $ clause) )
  where
    -- The clause is composed of the variables on the reason side which have
    -- at least one successor on the conflict side.  The value of the variable
    -- is the negation of its value under the current assignment.
    clause =
        foldl' (\ls i ->
                    if any (`elem` conflictSide cut) (Graph.suc (cutGraph cut) i)
                    then L (negate $ a!(V i)):ls
                    else ls)
               [] (reasonSide cut)
    maximum0 [] = 0            -- maximum0 has 0 as its max for the empty list
    maximum0 xs = maximum xs


-- | Annotate each variable in the conflict graph with literal (indicating its
-- assignment) and decision level.  The only reason we make a new datatype for
-- this is for its `Show' instance.
data CGNodeAnnot = CGNA Lit Level
instance Show CGNodeAnnot where
    show (CGNA (L 0) _) = "lam"
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
             -> gr CGNodeAnnot Int
mkConflGraph mFr lev reasonMap _dlits (cLit, confl) =
--     trace ("nodeSet = " ++ show nodeSet) $
    Graph.mkGraph nodes edges
  where
    -- we pick out all the variables from the conflict graph, specially adding
    -- both literals of the conflict variable, so that that variable has two
    -- nodes in the graph.
    nodes = ((0, CGNA (L 0) (-1)) :) $ -- lambda node
            ((unLit cLit, CGNA cLit (-1)) :) $
            ((negate (unLit cLit), CGNA (negate cLit) (lev!(var cLit))) :) $
            -- annotate each node with its literal and level
            map (\v -> (unVar v, CGNA (varToLit v) (lev!v))) $
            toList nodeSet
    -- edges are from variables (i.e. the number is > 0) that provide a reason
    -- for their destination variable, or from conflicting lits to lambda.
    edges = [ (x, y, 1)
            | (x, CGNA xLit _) <- nodes, (y, CGNA yLit _) <- nodes,
              xLit /= L 0 &&    -- no edge from lambda
              -- no edges between equal nodes
              x /= y &&
              x /= negate y && -- only occurs when x and y refer to `cLit',
                               -- in which case should be no edge
              if y == unLit cLit
              then -- edges to `cLit' are from `confl', the conflicting clause
                   negate (unLit xLit) `elem` map unLit confl
              else if y == 0
              then -- edges to lambda from conflicting lits
                   abs x == (abs . unLit) cLit
              else -- otherwise edges are from reasons
                   negate (unLit xLit) `elem`
                       map unLit (Map.findWithDefault [] (var yLit) reasonMap)
            ]
    -- node set includes all variables reachable from conflict, but not
    -- conflicting vars.  This node set construction needs a `seen' set
    -- because it might infinite loop otherwise.  The reason is that the
    -- `reason' array might implicitly represent a cyclic graph (which logic
    -- is perfectly capable of expressing) but which is "not helpful" for the
    -- implication graph.  So you cut a hole in the cycle at an arbitrary
    -- point (i.e. by ignoring the already-seen node when you discover the
    -- cycle).
    nodeSet = (`without` var cLit) $
              collectNodeSet BitSet.empty Set.empty
                                          (negate cLit : confl `without` cLit)
--     impliedBy lit | trace ("<<impliedBy " ++ show lit ++ ">>") $ False = undefined
    varToLit v = (if v `isTrueUnder` mFr then id else negate) $ L (unVar v)

    collectNodeSet :: BitSet Var -> Set Var -> [Lit] -> Set Var
    collectNodeSet _ set [] = set
    collectNodeSet seen set (lit:lits) =
        if haveSeen
        then collectNodeSet seen set lits
        else newSet `seq`
             collectNodeSet seen' newSet (lits ++ new)
      where
        haveSeen = var lit `BitSet.member` seen
        newSet = var lit `Set.insert` set
        new = filter ((var lit /=) . var) $ Map.findWithDefault [] (var lit) reasonMap
        seen' = var lit `BitSet.insert` seen

unfoldSet :: (Ord e) => (s -> (e, [s])) -> [s] -> Set e
unfoldSet g ss = let (es, sss) = unzip $ map g ss
                 in foldl' (flip Set.insert) Set.empty es
                    `Set.union` mapUnion (unfoldSet g) sss
    -- mapUnion defined to avoid intermediate lists expected with Set.unions
    -- (map f ...)
  where mapUnion _f []    = Set.empty
        mapUnion f (x:xs) = f x `Set.union` mapUnion f xs

-- | Unfold the implication graph backwards from the conflicting literal.
-- There is no root for the conflicting literal (but there is one for its
-- negation).
makeImpForest :: Map Var Clause -> (Lit, Clause) -> Forest Lit
makeImpForest reasonMap (cLit, conflicting) =
    unfoldForest (impliedBy reasonMap) [negate cLit]
    ++ unfoldForest (impliedBy reasonMap) (conflicting `without` cLit)
    where
      impliedBy reasonMap lit =
          (lit, filter ((var lit /=) . var) $
                Map.findWithDefault [] (var lit) reasonMap)

-- | Delete the assignment to last-assigned literal.  Undoes the trail, the
-- assignment, sets `noLevel', undoes reason.
undoOne :: MAssignment s -> DPLLMonad s ()
{-# INLINE undoOne #-}
undoOne m = do
  trl <- gets trail
  lvl <- gets level
  case trl of
    []       -> error "undoOne of empty trail"
    (l:trl') -> do
        lift $ m `unassign` l
        lift $ writeArray lvl (var l) noLevel
        modify $ \s ->
          s{ trail    = trl'
           , reason   = Map.delete (var l) (reason s) }

-- | Increase the recorded activity of given variable.
bump :: Var -> DPLLMonad s ()
{-# INLINE bump #-}
bump v = varOrderMod v (+ varInc)

varInc :: Double
varInc = 1.0
  


-- *** Impossible to satisfy

-- | /O(1)/.  Test for unsatisfiability.
--
-- The DPLL paper says, ''A problem is unsatisfiable if there is a conflicting
-- clause and there are no decision literals in @m@.''  But we were deciding
-- on all literals *without* creating a conflicting clause.  So now we also
-- test whether we've made all possible decisions, too.
unsat :: Maybe a -> DPLLStateContents s -> Bool
{-# INLINE unsat #-}
unsat maybeConflict (SC{dl=dl}) = isUnsat
    where isUnsat = (null dl && isJust maybeConflict)
                    -- or BitSet.size bad == numVars cnf



-- ** Helpers

-- *** Clause compaction

-- | Keep the smaller half of the learned clauses.
compact :: DPLLMonad s ()
compact = do
  n <- numVars `liftM` gets cnf
  lArr <- gets learnt
  clauses <- lift $ (nub . Fl.concat) `liftM`
                    forM [L (- n) .. L n]
                       (\v -> do val <- readArray lArr v ; writeArray lArr v []
                                 return val)
  let clauses' = take (length clauses `div` 2)
                 $ sortBy (comparing (length . snd)) clauses
  lift $ forM_ clauses'
           (\ wCl@(r, _) -> do
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
watchClause :: MAssignment s
            -> Clause
            -> Bool             -- ^ Is this clause learned?
            -> DPLLMonad s Bool
{-# INLINE watchClause #-}
watchClause m c isLearnt = do
  case c of
    [] -> return True
    [l] -> do result <- enqueue m l (Just c)
              levelArr <- gets level
              lift $ writeArray levelArr (var l) 0
              return result
    _ -> do
      let p = (negate (c !! 0), negate (c !! 1))
      r <- lift $ newSTRef p
      let annCl = (r, c)
          addCl arr = do modifyArray arr (fst p) $ const (annCl:)
                         modifyArray arr (snd p) $ const (annCl:)
      get >>= \s -> lift $ if isLearnt then addCl (learnt s) else addCl (watches s)
      return True

-- | Enqueue literal in the `propQ' and place it in the current assignment.
-- If this conflicts with an existing assignment, returns @False@; otherwise
-- returns @True@.  In case there is a conflict, the assignment is /not/
-- altered.
enqueue :: MAssignment s
        -> Lit                  -- ^ The literal that has been assigned true.
        -> Maybe Clause  -- ^ The reason for enqueuing the literal.  Including
                         -- a non-@Nothing@ value here adjusts the `reason'
                         -- map.
        -> DPLLMonad s Bool
{-# INLINE enqueue #-}
enqueue m l r = do
  mFr <- lift $ unsafeFreezeAss m
  case l `statusUnder` mFr of
    Right b -> return b         -- conflict/already assigned
    Left () -> do
      lift $ m `assign` l
      -- assign decision level for literal
      gets (level &&& (length . dl)) >>= \(levelArr, dlInt) ->
        lift (writeArray levelArr (var l) dlInt)
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
    vo <- varOrderArr `liftM` gets varOrder
    vActivity <- lift $ readArray vo v
    when (f vActivity > 1e100) $ rescaleActivities vo
    lift $ writeArray vo v (f vActivity)
  where
    rescaleActivities vo = lift $ do
        indices <- range `liftM` getBounds vo
        forM_ indices (\i -> modifyArray vo i $ const (* 1e-100))


-- | Retrieve the maximum-priority variable from the variable order.
varOrderGet :: IAssignment -> FrozenVarOrder -> Maybe Var
{-# INLINE varOrderGet #-}
varOrderGet mFr (FrozenVarOrder voFr) =
    let (v, _activity) = List.maximumBy (comparing snd) candidates
    in if List.null candidates then Nothing
       else Just v
  where
    varAssocs = assocs voFr
    (candidates, _unfit) = List.partition ((`isUndefUnder` mFr) . fst) varAssocs


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

-- | Modify a value inside the state.
modifySlot :: (MonadState s m) => (s -> a) -> (s -> a -> s) -> m ()
{-# INLINE modifySlot #-}
modifySlot slot f = modify $ \s -> f s (slot s)

-- | @modifyArray arr i f@ applies the function @f@ to the index @i@ and the
-- current value of the array at index @i@, then writes the result into @i@ in
-- the array.
modifyArray :: (Monad m, MArray a e m, Ix i) => a i e -> i -> (i -> e -> e) -> m ()
{-# INLINE modifyArray #-}
modifyArray arr i f = readArray arr i >>= writeArray arr i . (f i)

-- | Same as @newArray@, but helping along the type checker.
newSTUArray :: (MArray (STUArray s) e (ST s), Ix i)
               => (i, i) -> e -> ST s (STUArray s i e)
newSTUArray = newArray

newSTArray :: (MArray (STArray s) e (ST s), Ix i)
              => (i, i) -> e -> ST s (STArray s i e)
newSTArray = newArray

showAssignment a = intercalate " " ([show (a!i) | i <- range . bounds $ a,
                                                  (a!i) /= 0])

-- | Whether a list contains a single element.
isSingle :: [a] -> Bool
{-# INLINE isSingle #-}
isSingle [_] = True
isSingle _   = False

initialActivity :: Double
initialActivity = 1.0

instance Error (Lit, Clause) where
    noMsg = (L 0, [])

instance Error () where
    noMsg = ()


data Stats = Stats
    { statsNumConfl :: Int64
    , statsNumLearnt :: Int64
    , statsAvgLearntLen :: Double }

instance Show Stats where
    show s =
        "#c " ++ show (statsNumConfl s)
        ++ "/#l " ++ show (statsNumLearnt s)
        ++ " (avg len " ++ printf "%.2f" (statsAvgLearntLen s) ++ ")"

extractStats :: DPLLMonad s Stats
extractStats = do
  s <- get
  learntArr <- lift $ unsafeFreezeWatchArray (learnt s)
  let learnts = (nub . Fl.concat)
        [ map snd (learntArr!i) | i <- (range . bounds) learntArr ] :: [Clause]
      stats =
        Stats { statsNumConfl = fromIntegral (numConfl s)
              , statsNumLearnt = fromIntegral $ length learnts
              , statsAvgLearntLen =
                fromIntegral (foldl' (+) 0 (map length learnts))
                / fromIntegral (statsNumLearnt stats) }
  return stats

unsafeFreezeWatchArray :: WatchArray s -> ST s (Array Lit [WatchedPair s])
unsafeFreezeWatchArray = freeze

-- | Count the number of elements in the list that satisfy the predicate.
count :: (a -> Bool) -> [a] -> Int
count p = foldl' f 0
    where f x y = x + (if p y then 1 else 0)

argmin :: Ord b => (a -> b) -> a -> a -> a
argmin f x y = if f x <= f y then x else y

argminimum :: Ord b => (a -> b) -> [a] -> a
argminimum f = foldl1' (argmin f)

-- Replace buggy dominators code with my own.

type DomSets = [(Graph.Node,[Graph.Node],[Graph.Node])]

intersection :: [[Graph.Node]] -> [Graph.Node]
intersection cs = foldr intersect (head cs) cs

getdomv :: [Graph.Node] -> DomSets -> [[Graph.Node]]
getdomv vs  ds = [z|(w,_,z)<-ds,v<-vs,v==w]

builddoms :: DomSets -> [Graph.Node] -> DomSets
builddoms ds []     = ds
builddoms ds (v:vs) = builddoms ((fs++[(n,p,sort(n:idv))])++(tail rs)) vs
                      where idv     = intersection ((q \\ [n]):getdomv p ds)
                            (n,p,q) = head rs
                            (fs,rs) = span (\(x,_,_)->x/=v) ds

domr :: DomSets -> [Graph.Node] -> DomSets
domr ds vs|xs == ds  = ds
          |otherwise = domr xs vs
           where xs = (builddoms ds vs)

{-|
Finds the dominators relationship for a given graph and an initial
node. For each node v, it returns the list of dominators of v.
-}
dom :: Graph gr => gr a b -> Graph.Node -> [(Graph.Node,[Graph.Node])]
dom g u = map (\(x,_,z)->(x,z)) (domr ld n')
           where ld    = (u,[],[u]):map (\v->(v,Graph.pre g v,n)) (n')
                 n'    = n\\[u]
                 n     = Graph.nodes g

---------- TESTING ----------


-- | Verify the assigment is well-formed and satisfies the CNF problem.  This
-- function is run after a solution is discovered, just to be safe.
--
-- Makes sure each slot in the assignment is either 0 or contains its
-- (possibly negated) corresponding literal, and verifies that each clause is
-- made true by the assignment.
verify :: IAssignment -> CNF -> Bool
verify m cnf =
   -- m is well-formed
   Fl.all (\l -> m!(V l) == l || m!(V l) == negate l || m!(V l) == 0) [1..numVars cnf]
   && Fl.all (`isTrueUnder` m) (clauses cnf)
