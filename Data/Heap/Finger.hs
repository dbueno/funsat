{-# LANGUAGE   MultiParamTypeClasses
             , FlexibleInstances #-}

-- | A max-priority queue implemented with 2-3 finger trees.
module Data.Heap.Finger
#ifndef TESTING
    ( Info(..)
    , Heap
    , empty
    , null
    , insert
    , member
    , extractMax
    , increaseKey
    , fromList
    , Data.Heap.Finger.fmap' )
#endif
    where

import Prelude hiding ( foldr, elem, null )
import Data.Foldable ( foldr, elem )
import Data.Monoid
import Data.FingerTree hiding ( empty, null, fromList )
import qualified Data.FingerTree as FT

data Key a = NoKey | Key a deriving (Eq, Ord)

instance Monoid (Key a) where
    mempty = NoKey
    mappend k NoKey = k
    mappend _ k = k

-- | Info kept for each node in the tree.
data Info k a = Info { key :: k, datum :: a }
                deriving (Eq, Ord, Show)

-- descending ordered
newtype OrdSeq k a = OrdSeq (FingerTree (Key k) (Info k a))
    deriving Show

type Heap k a = OrdSeq k a

instance Measured (Key k) (Info k a) where
    measure = Key . key

empty :: (Ord k) => Heap k a
empty = OrdSeq FT.empty

null :: (Ord k) => Heap k a -> Bool
null (OrdSeq t) = FT.null t

insert :: (Ord k) => Info k a -> Heap k a -> Heap k a
insert info (OrdSeq xs) = OrdSeq (l >< (info <| r))
    where (l, r) = split (<= measure info) xs 

-- | Extract the value whose key is maximum.  If more than one key has maximum
-- value, an arbitrary one is chosen.
--
-- Precondition: The heap is non-empty.
extractMax :: (Ord k) => Heap k a -> (Info k a, Heap k a)
extractMax (OrdSeq s) = (x, OrdSeq s')
    where x :< s' = viewl s
                    
-- | @increaseKey old newKey h@.
--
-- Precondition: The old key must be in the heap, and the new key is no
-- smaller than the old.
increaseKey :: (Ord k, Eq a) =>
            Info k a              -- ^ old
            -> k                  -- ^ new
            -> Heap k a
            -> Heap k a
increaseKey oldInfo newKey (OrdSeq t) = OrdSeq (l' >< eqs' >< r')
    where (l, r)    = split (<= measure oldInfo) t
          (eqs, r') = split (< measure oldInfo) r
          eqs' = foldr (\i t' -> if i == oldInfo then t' else i <| t')
                 FT.empty eqs
           -- newInfo is bigger, so must fit on bigger side of split
          (OrdSeq l') = insert newInfo (OrdSeq l)
          newInfo = oldInfo{ key = newKey }

member :: (Ord k, Eq a) => Info k a -> Heap k a -> Bool
member x (OrdSeq t) = x `elem` t

fromList :: (Ord k) => [Info k a] -> Heap k a
fromList = foldr insert empty


------------------------------------------------------------------------
-- Helpers



fmap' f (OrdSeq t) = OrdSeq $ FT.fmap' f t