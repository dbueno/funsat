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
import Data.Int (Int64)
import Data.List (intercalate, nub, tails, sortBy)
import Data.Map (Map)
import Data.Maybe
import Data.Ord (comparing)
import Data.STRef
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Tree
import Debug.Trace (trace)
import System.Random
import System.IO.Unsafe (unsafePerformIO)
import System.IO (hPutStr, stderr)
import Text.Printf( printf )
import qualified Data.BitSet as BitSet
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
    SC{ cnf=f, dl=[], bad=BitSet.empty, rnd=g
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
    show l = if ul < 0 then "~" ++ show (abs ul) else show ul
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

-- | A /level array/ maintains a record of the decision level of each variable
-- in the solver.  If @level@ is such an array, then @level[i] == j@ means the
-- decision level for var number @i@ is @j@.  @j@ must be non-negative when
-- the level is defined, and `noLevel' otherwise.
--
-- Whenever an assignment of variable @v@ is made at decision level @i@,
-- @level[unVar v]@ is set to @i@.
type LevelArray s = STUArray s Var Int
-- | Immutable version.
type FrozenLevelArray = UArray Var Int

-- | Value of the `level' array if corresponding variable unassigned.  Had
-- better be less that 0.
noLevel :: Int
noLevel = -1

-- | The VSIDS-like dynamic variable ordering.
newtype VarOrder s = VarOrder { varOrderArr :: STUArray s Var Double }
    deriving Show
newtype FrozenVarOrder = FrozenVarOrder (UArray Var Double)
    deriving Show

type BadBag = BitSet Var

-- | Each pair of watched literals is paired with its clause.
type WatchedPair s = (STRef s (Lit, Lit), Clause)
type WatchArray s = STArray s Lit [WatchedPair s]

-- ** DPLL State and Phases

data DPLLStateContents s = SC
    { cnf :: CNF                -- ^ The problem.
    , dl :: [Lit]
      -- ^ The decision level (last decided literal on front).
    , bad :: BadBag
      -- ^ Bag of /bad/ variables.
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
             (\ f l -> lift . lift $ readArray ws l >>= writeArray ws l . f))
           {-# SCC "bcpLearnts" #-} forM_ (tails learnts) (updateWatches
             (\ f l -> lift . lift $ readArray ls l >>= writeArray ls l . f))
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

-- | Non-chronological backtracking.  The current implementation finds all the
-- decision literals responsible for the current conflict, and the learnt
-- clause is derived from these.  The learnt clause is also here added to the
-- database and the asserting literal is enqueued.
backJump :: MAssignment s
         -> (Lit, Clause)
            -- ^ @(l, c)@, where attempting to assign @l@ conflicted with
            -- clause @c@.
         -> DPLLMonad s (Maybe (MAssignment s))
backJump m (_, conflict) = get >>= \(SC{dl=dl, bad=bad}) -> do
    modify $ \s -> s{numConfl = numConfl s + 1}
    levelArr :: FrozenLevelArray <- do s <- get
                                       lift $ unsafeFreeze (level s)
    learntCl <- analyse levelArr
    s  <- get
    let levels = map ((levelArr !) . var) (learntCl `without` negate (head dl))
        conflictAt0 = if null levels then False else 0 == List.maximum levels
        btLevel = if null levels then length dl - 1 else List.maximum levels
        numDecisionsToUndo = length dl - btLevel
        (undone_ld : dl') = drop (numDecisionsToUndo - 1) dl
        undoneLits = takeWhile (\lit -> levelArr ! (var lit) > btLevel) (trail s)
--    mFr <- lift $ unsafeFreezeAss m
--     trace ("bt: " ++ show (length dl) ++ "/" ++ show btLevel
--                  ++ ", l = " ++ show l ++ ", undone_ld = " ++ show undone_ld
--                  ++ ", conflict = " ++ show conflict
--                  ++ "\n  trail = " ++ show (trail s)
--                  ++ "\n  mFr = " ++ showAssignment mFr
--                  ++ "\n  dl = " ++ show dl
--                  ++ "\n  dl' = " ++ show dl'
--                  ++ "\n  levelArr = " ++ show levelArr
--                  ++ "\n  bad = " ++ show bad
--                  ++ "\n  numConfl = " ++ show (numConfl s)
--                  ++ "\n  learnt clause: " ++ show learntCl
--                  ++ ", " ++ show (learntCl `statusUnder` mFr)
--                  ++ "\n  reason = " ++ Map.showTree (reason s)) $
--     trace ("  new m = " ++ showAssignment m') $
    forM_ undoneLits $ const (undoOne m)
    mFr <- lift $ unsafeFreezeAss m
    assert (numDecisionsToUndo > 0) $
     assert (not (null learntCl)) $
     assert (learntCl `isUnitUnder` mFr) $
     assert (learntCl `contains` negate (head dl)) $
     modify $ \s ->
      s{ dl  = dl'
       , bad = if null dl' then bad `with` var undone_ld else bad }
    forM_ conflict (bump . var)
    enqueue m (negate (head dl)) (Just learntCl)
    watchClause m learntCl True
    return $ if conflictAt0 then Nothing else Just m
  where
    -- Returns learnt clause.
    analyse levelArr = do
      st <- get
      let impForest :: Forest Lit = makeImpForest (reason st)
          learntCl = negate (head (dl st)):rel_sat levelArr (dl st) impForest
      return . nub $ learntCl

    -- Unfold the implication graph backwards from the conflict.
    makeImpForest reasonM = unfoldForest (impliedBy reasonM) conflict
    impliedBy reasonM lit = (lit, Map.findWithDefault [] (var lit) reasonM)

    -- STRATEGY 1: Find the decision literals responsible for current conflict.
    _findDecisions levelArr _ ts =
        bfsPick levelArr ts (\ _ antecedents -> null antecedents)

    -- STRATEGY 2: Rel_sat.
    rel_sat levelArr dlits ts =
        let currentDecLev = length dlits
        in bfsPick levelArr ts (\ (_, lev) _ -> lev < currentDecLev)

    -- Perform a BFS on the reverse implication graph, returning the first
    -- literals satisfying p.  Each literal will be passed to p at most once,
    -- and no antecedents of p are explored.  Only literals above decision level
    -- 0 which are not the conflict liteal are passed to p.
    bfsPick :: FrozenLevelArray
            -> Forest Lit -> ((Lit, Int) -> Forest Lit -> Bool) -> [Lit]
    bfsPick levelArr ts p = bfsPicker BitSet.empty p ts
      where
        bfsPicker :: BitSet Var
                  -> ((Lit, Int) -> Forest Lit -> Bool) -> Forest Lit -> [Lit]
        bfsPicker _ _ [] = []
        bfsPicker seen p (t:ts) =
            if isSeen then bfsPicker seen' p ts
            else if litLevel > 0 && p (lit, litLevel) antecedents
            then lit : bfsPicker seen' p ts
            else bfsPicker seen' p (ts ++ antecedents)
            
          where
            litLevel    = levelArr ! (var lit)
            isSeen      = seen `contains` var lit
            seen'       = seen `with` var lit
            lit         = rootLabel t
            antecedents = subForest t

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
unsat maybeConflict (SC{cnf=cnf, dl=dl, bad=bad}) = isUnsat
    where isUnsat = (null dl && isJust maybeConflict)
                    || BitSet.size bad == numVars cnf



-- ** Helpers

-- | Keep the smaller half of the learnt clauses.
compact :: DPLLMonad s ()
compact = do
  n <- numVars `liftM` gets cnf
  lArr <- gets learnt
  clauses <- lift $ (nub . Fl.concat) `liftM`
             sequence [ do val <- readArray lArr v ; writeArray lArr v []
                           return val
                        | v <- [L (- n) .. L n] ]
  let clauses' = take (length clauses `div` 2)
                 $ sortBy (comparing (length . snd)) clauses
  lift $ forM_ clauses'
           (\ wCl@(r, _) -> do
              (x, y) <- readSTRef r
              readArray lArr x >>= writeArray lArr x . (wCl:)
              readArray lArr y >>= writeArray lArr y . (wCl:))
              

-- | Add clause to the watcher lists, unless clause is a singleton; if clause
-- is a singleton, `enqueue's fact and returns `False' if fact is in conflict,
-- `True' otherwise.  This function should be called exactly once per clause,
-- per run.  It should not be called to reconstruct the watcher list when
-- propagating.
--
-- Currently the watched literals in each clause are the first two.
watchClause :: MAssignment s
            -> Clause
            -> Bool             -- ^ Is this clause learnt?
            -> DPLLMonad s Bool
{-# INLINE watchClause #-}
watchClause m c isLearnt = do
  case c of
    [] -> return True
    [l] -> enqueue m l (Just c)
    _ -> do
      let p = (negate (c !! 0), negate (c !! 1))
      r <- lift $ newSTRef p
      let annCl = (r, c)
          addCl arr = do readArray arr (fst p) >>= writeArray arr (fst p) . (annCl:)
                         readArray arr (snd p) >>= writeArray arr (snd p) . (annCl:)
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

-- | Same as @newArray@, but helping along the type checker.
newSTUArray :: (MArray (STUArray s) e (ST s), Ix i)
               => (i, i) -> e -> ST s (STUArray s i e)
newSTUArray = newArray

newSTArray :: (MArray (STArray s) e (ST s), Ix i)
              => (i, i) -> e -> ST s (STArray s i e)
newSTArray = newArray

showAssignment a = intercalate " " ([show (a!i) | i <- range . bounds $ a,
                                                  (a!i) /= 0])

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
        forM_ indices (\i -> readArray vo i >>= writeArray vo i . (* 1e-100))


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

-- | Whether a list contains a single element.
isSingle :: [a] -> Bool
{-# INLINE isSingle #-}
isSingle [_] = True
isSingle _   = False


{-# INLINE modifySlot #-}
modifySlot slot f = modify $ \s -> f s (slot s)

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
  let learnts = nub [ map snd (learntArr!i) | i <- (range . bounds) learntArr ]
      stats =
        Stats { statsNumConfl = fromIntegral (numConfl s)
              , statsNumLearnt = fromIntegral $ length learnts
              , statsAvgLearntLen =
                fromIntegral (foldl' (+) 0 (map length learnts))
                / fromIntegral (statsNumLearnt stats) }
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
verify :: IAssignment -> CNF -> Bool
verify m cnf =
   -- m is well-formed
   Fl.all (\l -> m!(V l) == l || m!(V l) == negate l || m!(V l) == 0) [1..numVars cnf]
   && Fl.all (`isTrueUnder` m) (clauses cnf)
