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



-- | Data types used when dealing with SAT problems in funsat.
module Funsat.Types where


import Control.Monad.MonadST( MonadST(..) )
import Control.Monad.ST.Strict
import Data.Array.ST
import Data.Array.Unboxed
import Data.BitSet (BitSet)
import Data.Foldable hiding (sequence_)
import Data.Map (Map)
import Data.Set (Set)
import Funsat.Monad
import Funsat.Utils
import Prelude hiding (sum, concatMap, elem, foldr, foldl, any, maximum)
import qualified Data.BitSet as BitSet
import qualified Data.Foldable as Fl
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set


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

-- | The polarity of the literal.  Negative literals are false; positive
-- literals are true.  The 0-literal is an error.
litSign :: Lit -> Bool
litSign (L x) | x < 0 = False
              | x > 0 = True

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
-- that I can easily get a `Foldable' instance.
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

-- | Mutable array corresponding to the `IAssignment' representation.
type MAssignment s = STUArray s Var Int

-- | Same as @freeze@, but at the right type so GHC doesn't yell at me.
freezeAss :: MAssignment s -> ST s IAssignment
{-# INLINE freezeAss #-}
freezeAss = freeze
-- | See `freezeAss'.
unsafeFreezeAss :: (MonadST s m) => MAssignment s -> m IAssignment
{-# INLINE unsafeFreezeAss #-}
unsafeFreezeAss = liftST . unsafeFreeze

thawAss :: IAssignment -> ST s (MAssignment s)
{-# INLINE thawAss #-}
thawAss = thaw
unsafeThawAss :: IAssignment -> ST s (MAssignment s)
{-# INLINE unsafeThawAss #-}
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

-- | Whether all the elements of the model in the list are false but one, and
-- none is true, under the model.
isUnitUnder :: (Model a m) => [a] -> m -> Bool
{-# SPECIALISE INLINE isUnitUnder :: Clause -> IAssignment -> Bool #-}
isUnitUnder c m = isSingle (filter (not . (`isFalseUnder` m)) c)
                  && not (Fl.any (`isTrueUnder` m) c)

-- Precondition: clause is unit.
-- getUnit :: (Model a m, Show a, Show m) => [a] -> m -> a
-- getUnit c m | trace ("getUnit " ++ show c ++ " " ++ showAssignment m) $ False = undefined

-- | Get the element of the list which is not false under the model.  If no
-- such element, throws an error.
getUnit :: (Model a m, Show a) => [a] -> m -> a
{-# SPECIALISE INLINE getUnit :: Clause -> IAssignment -> Lit #-}
getUnit c m = case filter (not . (`isFalseUnder` m)) c of
                [u] -> u
                xs   -> error $ "getUnit: not unit: " ++ show xs
