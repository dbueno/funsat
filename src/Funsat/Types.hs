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

{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}



-- | Data types used when dealing with SAT problems in funsat.
module Funsat.Types where


import Data.Array.ST
import Data.Array.Unboxed
import Data.BitSet ( BitSet )
import Data.Foldable hiding ( sequence_ )
import Data.Int( Int64 )
import Data.List( intercalate )
import Data.Map ( Map )
import Data.Set ( Set )
import Data.STRef
import Prelude hiding ( sum, concatMap, elem, foldr, foldl, any, maximum )
import qualified Data.BitSet as BitSet
import qualified Data.Foldable as Fl
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set



-- * Basic Types

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

instance Num Lit where
    _ + _ = error "+ doesn't make sense for literals"
    _ - _ = error "- doesn't make sense for literals"
    _ * _ = error "* doesn't make sense for literals"
    signum _ = error "signum doesn't make sense for literals"
    negate   = inLit negate
    abs      = inLit abs
    fromInteger l | l == 0    = error "0 is not a literal"
                  | otherwise = L $ fromInteger l

-- | Transform the number inside the literal.
inLit :: (Int -> Int) -> Lit -> Lit
inLit f = L . f . unLit

-- | The polarity of the literal.  Negative literals are false; positive
-- literals are true.  The 0-literal is an error.
litSign :: Lit -> Bool
litSign (L x) | x < 0     = False
              | x > 0     = True
              | otherwise = error "litSign of 0"

instance Show Lit where show = show . unLit
instance Read Lit where
    readsPrec i s = map (\(i,s) -> (L i, s)) (readsPrec i s)

-- | The variable for the given literal.
var :: Lit -> Var
var = V . abs . unLit

-- | The positive literal for the given variable.
lit :: Var -> Lit
lit = L . unVar

type Clause = [Lit]

data CNF = CNF
    { numVars    :: Int
    , numClauses :: Int
    , clauses    :: Set Clause } deriving (Show, Read, Eq)

-- | The solution to a SAT problem.  In each case we return an assignment,
-- which is obviously right in the `Sat' case; in the `Unsat' case, the reason
-- is to assist in the generation of an unsatisfiable core.
data Solution = Sat !IAssignment | Unsat !IAssignment deriving (Eq)

instance Show Solution where
   show (Sat a)     = "satisfiable: " ++ showAssignment a
   show (Unsat _)   = "unsatisfiable"

finalAssignment :: Solution -> IAssignment
finalAssignment (Sat a)   = a
finalAssignment (Unsat a) = a




-- | Represents a container of type @t@ storing elements of type @a@ that
-- support membership, insertion, and deletion.
--
-- There are various data structures used in funsat which are essentially used
-- as ''set-like'' objects.  I've distilled their interface into three
-- methods.  These methods are used extensively in the implementation of the
-- solver.
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

-- * Assignments


-- | An ''immutable assignment''.  Stores the current assignment according to
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

showAssignment :: IAssignment -> String
showAssignment a = intercalate " " ([show (a!i) | i <- range . bounds $ a,
                                                  (a!i) /= 0])


-- | Mutable array corresponding to the `IAssignment' representation.
type MAssignment s = STUArray s Var Int

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

-- | Annotate each variable in the conflict graph with literal (indicating its
-- assignment) and decision level.  The only reason we make a new datatype for
-- this is for its `Show' instance.
data CGNodeAnnot = CGNA Lit Int

-- | Just a graph with special node annotations.
type ConflictGraph g = g CGNodeAnnot ()

-- | The lambda node is connected exactly to the two nodes causing the conflict.
cgLambda :: CGNodeAnnot
cgLambda = CGNA (L 0) (-1)

instance Show CGNodeAnnot where
    show (CGNA (L 0) _) = "lambda"
    show (CGNA l lev) = show l ++ " (" ++ show lev ++ ")"



-- * Model


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
        where
          isFalseUnder x m = isFalse $ x `statusUnder` m
              where isFalse (Right False) = True
                    isFalse _             = False

-- * Internal data types

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


-- | The VSIDS-like dynamic variable ordering.
newtype VarOrder s = VarOrder { varOrderArr :: STUArray s Var Double }
    deriving Show
newtype FrozenVarOrder = FrozenVarOrder (UArray Var Double)
    deriving Show

-- | Each pair of watched literals is paired with its clause and id.
type WatchedPair s = (STRef s (Lit, Lit), Clause, ClauseId)
type WatchArray s = STArray s Lit [WatchedPair s]

data PartialResolutionTrace = PartialResolutionTrace
    { resTraceIdCount         :: !Int
    , resTrace                :: ![Int]
    , resTraceOriginalSingles :: ![(Clause, ClauseId)]
      -- Singleton clauses are not stored in the database, they are assigned.
      -- But we need to record their ids, so we put them here.
    , resSourceMap            :: Map ClauseId [ClauseId] } deriving (Show)

type ReasonMap = Map Var (Clause, ClauseId)
type ClauseId = Int

instance Show (STRef s a) where show = const "<STRef>"
instance Show (STUArray s Var Int) where show = const "<STUArray Var Int>"
instance Show (STUArray s Var Double) where show = const "<STUArray Var Double>"
instance Show (STArray s a b) where show = const "<STArray>"


-- * Configuration

-- | A choice of conflict graph cut for learning clauses.
data ConflictCut = FirstUipCut
                 | DecisionLitCut
                   deriving (Show)

-- | Configuration parameters for the solver.
data FunsatConfig = Cfg
    { configRestart :: !Int64      -- ^ Number of conflicts before a restart.
    , configRestartBump :: !Double -- ^ `configRestart' is altered after each
                                   -- restart by multiplying it by this value.
    , configUseVSIDS :: !Bool      -- ^ If true, use dynamic variable ordering.
    , configUseRestarts :: !Bool
    , configCut :: !ConflictCut
    }
                  deriving (Show)

