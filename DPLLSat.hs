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

Goal: A reasonably efficient, easy-to-understand modern sat solver.  I want it
as architecturally simple as the description in /Abstract DPLL and Abstract
DPLL Modulo Theories/ is conceptually, while retaining some efficient
optimisations.

            Current state: decision heuristic\/code cleanup\/tests.

* 24 Apr 2008 16:47:56

After some investigating, mad coding, and cursing, First UIP clause learning
has been implemented.  For conceptual clarity, though, it is implemented in
terms of an explicit conflict graph, explicit dominator calculation, and
explicit cuts.  Profiling shows that for conflict-heavy problems,
conflict-clause generation is no more a bottleneck than boolean constraint
propagation.

This can and will be improved later.

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
        , Stats(..)
        , CNF
        , GenCNF(..)
        , NonStupidString(..)
        , statTable
        , verify
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


import Control.Arrow ((&&&))
import Control.Exception (assert)
import Control.Monad.Error hiding ((>=>), forM_)
import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Data.Array.ST
import Data.Array.Unboxed
import Data.BitSet (BitSet)
import Data.Foldable hiding (sequence_)
import Data.Graph.Inductive.Graph( DynGraph, Graph )
import Data.Graph.Inductive.Graphviz
import Data.Graph.Inductive.Tree( Gr )
import Data.Int (Int64)
import Data.List (intercalate, nub, tails, sortBy, intersect)
import Data.Map (Map)
import Data.Maybe
import Data.Ord (comparing)
import Data.STRef
import Data.Sequence (Seq)
import Data.Set (Set)
import Debug.Trace (trace)
import Prelude hiding (sum, concatMap, elem, foldr, foldl, any, maximum)
import System.Random
import Text.Printf( printf )
import Utils
import qualified Data.BitSet as BitSet
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.BFS as BFS
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.Foldable as Fl
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified FastDom as Dom
import qualified Text.Tabular as Tabular

-- * Interface

-- | Run the DPLL-based SAT solver on the given CNF instance.
solve :: DPLLConfig -> StdGen -> CNF -> (Solution, Stats)
solve cfg g fIn =
    -- To solve, we simply take baby steps toward the solution using solveStep,
    -- starting with an initial assignment.
--     trace ("input " ++ show f) $
    runST $
    evalStateT (do sol <- stepToSolution $ do
                     initialAssignment <- lift $ newSTUArray (V 1, V (numVars f)) 0
                     isUnsat <- initialState initialAssignment
                     if isUnsat then return (Right Unsat)
                      else solveStep initialAssignment
                   stats <- extractStats
                   return (sol, stats))
    SC{ cnf=f{clauses = Set.empty}, dl=[], rnd=g
      , watches=undefined, learnt=undefined, propQ=Seq.empty
      , trail=[], numConfl=0, level=undefined, numConflTotal=0
      , numDecisions=0, numImpl=0
      , reason=Map.empty, varOrder=undefined
      , dpllConfig=cfg }
  where
    f = preprocessCNF fIn
    -- If returns True, then problem is unsat.
    initialState :: MAssignment s -> DPLLMonad s Bool
    initialState m = do
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
solve1 :: CNF -> (Solution, Stats)
solve1 f = solve (defaultConfig f) (mkStdGen 1) f

-- | Configuration parameters for the solver.
data DPLLConfig = Cfg
    { configRestart :: Int64      -- ^ Number of conflicts before a restart.
    , configRestartBump :: Double -- ^ `configRestart' is altered after each
                                  -- restart by multiplying it by this value.
    , configUseVSIDS :: Bool      -- ^ If true, use dynamic variable ordering.
    , configUseWatchedLiterals :: Bool -- ^ If true, use watched literals
                                       -- scheme.
    , configUseRestarts :: Bool }
                  deriving Show

-- | A default configuration based on the formula to solve.
defaultConfig :: CNF -> DPLLConfig
defaultConfig _f = Cfg { configRestart = 100
                       , configRestartBump = 1.5
                       , configUseVSIDS = True
                       , configUseWatchedLiterals = True
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
simplifyDB :: IAssignment -> DPLLMonad s ()
simplifyDB _mFr = undefined

-- * Internals

-- | The DPLL procedure is modeled as a state transition system.  This
-- function takes one step in that transition system.  Given an unsatisfactory
-- assignment, perform one state transition, producing a new assignment and a
-- new state.
solveStep :: MAssignment s -> DPLLMonad s (Step s)
solveStep m = do
    lift (unsafeFreezeAss m) >>= solveStepInvariants
    conf <- gets dpllConfig
    -- let selector = if configUseVSIDS conf then select else selectStatic
    let bcper = if configUseWatchedLiterals conf then bcp else bcpDumb
    maybeConfl <- bcper m
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
data Solution = Sat IAssignment | Unsat deriving (Eq)

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
                     (do stats <- extractStats
                         trace ("Restarting...") $
                          trace (statSummary stats) $
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
      modify $ \s -> s{ dl = [], propQ = Seq.empty }
      compact

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

-- isUnitUnder c m | trace ("isUnitUnder " ++ show c ++ " " ++ showAssignment m) $ False = undefined
isUnitUnder c m = isSingle (filter (not . (`isFalseUnder` m)) c)
                  && not (Fl.any (`isTrueUnder` m) c)

-- Precondition: clause is unit.
-- getUnit :: (Model a m, Show a, Show m) => [a] -> m -> a
-- getUnit c m | trace ("getUnit " ++ show c ++ " " ++ showAssignment m) $ False = undefined
getUnit c m = case filter (not . (`isFalseUnder` m)) c of
                [u] -> u
                xs   -> error $ "getUnit: not unit: " ++ show xs

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
    , numConfl :: !Int64
      -- ^ The number of conflicts that have occurred since the last restart.
    , numConflTotal :: !Int64
      -- ^ The total number of conflicts.
    , numDecisions :: !Int64
      -- ^ The total number of decisions.
    , numImpl :: !Int64
      -- ^ The total number of implications (propagations).
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
             lift $ modify $ \s -> s{ numImpl = numImpl s + 1 }
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

bcpDumb :: MAssignment s -> DPLLMonad s (Maybe (Lit, Clause))
bcpDumb m = do
  mFr <- lift $ freezeAss m
  s <- get
  let candidates = Set.filter (not . (`isTrueUnder` mFr)) (clauses . cnf $ s)
  case find (`isFalseUnder` mFr) candidates of
    Just fClause -> return $ Just (head fClause, fClause)
    Nothing ->
      case find (`isUnitUnder` mFr) candidates of
        Nothing -> return Nothing
        Just clause -> do
          let unitLit = getUnit clause mFr
          modify $ \s -> s{ numImpl = numImpl s + 1 }
          isConsistent <- assert (unitLit `isUndefUnder` mFr) $
                          enqueue m unitLit (Just clause)
          clearQueue
          if not isConsistent
           then return $ Just (unitLit, clause)
           else bcpDumb m


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
         -> (Lit, Clause)
            -- ^ @(l, c)@, where attempting to assign @l@ conflicted with
            -- clause @c@.
         -> DPLLMonad s (Maybe (MAssignment s))
backJump m c@(_, conflict) = get >>= \(SC{dl=dl, reason=_reason}) -> do
    _theTrail <- gets trail
--     trace ("********** conflict = " ++ show c) $ return ()
--     trace ("trail = " ++ show _theTrail) $ return ()
--     trace ("dlits (" ++ show (length dl) ++ ") = " ++ show dl) $ return ()
--          ++ "reason: " ++ Map.showTree _reason
--           ) (
    modify $ \s -> s{ numConfl = numConfl s + 1
                    , numConflTotal = numConflTotal s + 1 }
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
    mFr <- lift $ unsafeFreezeAss m
--     trace ("new mFr: " ++ showAssignment mFr) $ return ()
    -- TODO once I'm sure this works I don't need getUnit, I can just use the
    -- uip of the cut.
    enqueue m (getUnit learntCl mFr) (Just learntCl) -- learntCl is asserting
    watchClause m learntCl True
    return $ Just m


-- analyse' :: IAssignment -> FrozenLevelArray -> [Lit] -> (Lit, Clause)
--         -> DPLLMonad s (Clause, Int) -- ^ learned clause and new decision
--                                      -- level
-- analyse' mFr levelArr dlits c@(cLit, _cClause) = do
--     st <- get
--     let (learntCl, newLevel) = cutLearn mFr levelArr firstUIPCut
--         firstUIPCut = undefined

--         backBFS (seen :: BitSet Var) = undefined
--         -- node x top. l.t. y
--         x <| y = let (_prec_x, xsuff) = break (==x) tsNodes
--                  in y `elem` xsuff
--         conflGraph = mkConflGraph mFr levelArr (reason st) dlits c
--                      :: Gr CGNodeAnnot ()
--         rconflGraph = grev conflGraph
--         bfsNodes = BFS.bfs 0 rconflGraph
--         tsNodes  = DFS.topsort rconflGraph

--     return $ (learntCl, newLevel)
                  

-- | Analyse a the conflict graph and produce a learned clause.  We use the
-- First UIP cut of the conflict graph.
analyse :: IAssignment -> FrozenLevelArray -> [Lit] -> (Lit, Clause)
        -> DPLLMonad s (Clause, Int) -- ^ learned clause and new decision
                                     -- level
analyse mFr levelArr dlits c@(cLit, _cClause) = do
    st <- get
--     trace ("mFr: " ++ showAssignment mFr) $ assert True (return ())
    let (learntCl, newLevel) = cutLearn mFr levelArr firstUIPCut
        firstUIPCut = uipCut dlits levelArr conflGraph (unLit cLit)
                      (firstUIP conflGraph)
        conflGraph = mkConflGraph mFr levelArr (reason st) dlits c
                     :: Gr CGNodeAnnot ()
--     trace ("graphviz graph:\n" ++ graphviz' conflGraph) $ return ()
--     trace ("cut: " ++ show firstUIPCut) $ return ()
--     trace ("topSort: " ++ show topSortNodes) $ return ()
--     trace ("dlits (" ++ show (length dlits) ++ "): " ++ show dlits) $ return ()
--     trace ("learnt: " ++ show (map (\l -> (l, levelArr!(var l))) learntCl, newLevel)) $ return ()
--     outputConflict "conflict.dot" (graphviz' conflGraph) $ return ()
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
              if negate conflNode `elem` DFS.reachable (abs $ unLit lastd) conflGraph
              then 
                  filter (\i -> levelN i == currentLevel && i /= conflNode) $
                  fromJust $ lookup (negate conflNode) domFromLastd
              else [(abs $ unLit lastd)]
          domFromLastd = Dom.dom conflGraph (abs $ unLit lastd)
          distanceFromConfl x = length $ BFS.esp x conflNode conflGraph

    -- helpers
    lastd        = head dlits
    conflNode    = unLit cLit
    currentLevel = length dlits
    levelN i = if i == unLit cLit then currentLevel else ((levelArr!) . V . abs) i

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
  conf <- gets dpllConfig
  case c of
    [] -> return True
    [l] -> do result <- enqueue m l (Just c)
              levelArr <- gets level
              lift $ writeArray levelArr (var l) 0
              return result
    _ -> if configUseWatchedLiterals conf then
             do let p = (negate (c !! 0), negate (c !! 1))
                r <- lift $ newSTRef p
                let annCl = (r, c)
                    addCl arr = do modifyArray arr (fst p) $ const (annCl:)
                                   modifyArray arr (snd p) $ const (annCl:)
                get >>= lift . addCl . (if isLearnt then learnt else watches)
                return True
         else do modify $ \s ->
                     let cs = c `Set.insert` (clauses . cnf) s
                     in s{ cnf = (cnf s){ clauses = cs
                                        , numClauses = Set.size cs } }
                 return True

-- | Enqueue literal in the `propQ' and place it in the current assignment.
-- If this conflicts with an existing assignment, returns @False@; otherwise
-- returns @True@.  In case there is a conflict, the assignment is /not/
-- altered.
--
-- Also records decision level, modifies trail, and records reason for
-- assignment.
enqueue :: MAssignment s
        -> Lit                  -- ^ The literal that has been assigned true.
        -> Maybe Clause  -- ^ The reason for enqueuing the literal.  Including
                         -- a non-@Nothing@ value here adjusts the `reason'
                         -- map.
        -> DPLLMonad s Bool
{-# INLINE enqueue #-}
-- enqueue _m l _r | trace ("enqueue " ++ show l) $ False = undefined
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

showAssignment a = intercalate " " ([show (a!i) | i <- range . bounds $ a,
                                                  (a!i) /= 0])

initialActivity :: Double
initialActivity = 1.0

instance Error (Lit, Clause) where
    noMsg = (L 0, [])

instance Error () where
    noMsg = ()


data Stats = Stats
    { statsNumConfl :: Int64
    , statsNumConflTotal :: Int64
    , statsNumLearnt :: Int64
    , statsAvgLearntLen :: Double
    , statsNumDecisions :: Int64
    , statsNumImpl :: Int64 }

-- the show instance uses the wrapped string.
newtype NonStupidString = Stupid { stupefy :: String }
instance Show NonStupidString where
    show = stupefy

instance Show Stats where
    show = show . statTable

statTable :: Stats -> Tabular.T NonStupidString
statTable s =
    Tabular.mkTable
                   [ [Stupid "Num. Conflicts"
                     ,Stupid $ show (statsNumConflTotal s)]
                   , [Stupid "Num. Learned Clauses"
                     ,Stupid $ show (statsNumLearnt s)]
                   , [Stupid " --> Avg. Lits/Clause"
                     ,Stupid $ show (statsAvgLearntLen s)]
                   , [Stupid "Num. Decisions"
                     ,Stupid $ show (statsNumDecisions s)]
                   , [Stupid "Num. Propagations"
                     ,Stupid $ show (statsNumImpl s)] ]

statSummary :: Stats -> String
statSummary s =
     show (Tabular.mkTable
           [[Stupid $ show (statsNumConflTotal s) ++ " Conflicts"
            ,Stupid $ "| " ++ show (statsNumLearnt s) ++ " Learned Clauses"
                      ++ " (avg " ++ printf "%.2f" (statsAvgLearntLen s)
                      ++ " lits/clause)"]])


extractStats :: DPLLMonad s Stats
extractStats = do
  s <- get
  learntArr <- lift $ unsafeFreezeWatchArray (learnt s)
  let learnts = (nub . Fl.concat)
        [ map snd (learntArr!i) | i <- (range . bounds) learntArr ] :: [Clause]
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

---------- TESTING ----------


-- | Verify the assigment is well-formed and satisfies the CNF problem.  This
-- function is run after a solution is discovered, just to be safe.
--
-- Makes sure each slot in the assignment is either 0 or contains its
-- (possibly negated) corresponding literal, and verifies that each clause is
-- made true by the assignment.
verify :: IAssignment -> CNF -> Maybe [(Clause, Either () Bool)]
verify m cnf =
   -- m is well-formed
--    Fl.all (\l -> m!(V l) == l || m!(V l) == negate l || m!(V l) == 0) [1..numVars cnf]
   let unsatClauses = toList $
                      Set.filter (not . isTrue . snd) $
                      Set.map (\c -> (c, c `statusUnder` m)) (clauses cnf)
   in if null unsatClauses
      then Nothing
      else Just unsatClauses
  where isTrue (Right True) = True
        isTrue _            = False