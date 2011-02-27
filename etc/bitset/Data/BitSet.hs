-- | A /bit set/ maintains a record of members from a type that can be mapped
-- into (non-negative) @Int@s. The maximum number of elements that can be
-- stored is @maxbound :: Int@. Supports insertion, deletion, size, and
-- membership testing, and is completely pure (functional).
--
-- To use this library, simply supply a `Enum' instance for your data type or
-- have it derived. It is important that the values you intend to keep track
-- of start from 0 and go up. A value for which @fromEnum x@ is @n@
-- corresponds to bit location @n@ in an @Integer@, and thus requires that
-- @Integer@ to have at least @n@ bits.
--
-- The implementation is quite simple: we rely on the @Bits Integer@ instance
-- from @Data.Bits@.  An advantage of this library over simply using that
-- @Bits@ instance is the phantom type parameter used in the `BitSet' type.
-- The interface we expose ensures client code will not typecheck if it
-- confuses two bit sets intended to keep track of different types.
module Data.BitSet
    ( BitSet
    , empty
    , null
    , insert
    , fromList
    , delete
    , member
    , size
    , toIntegral
    , unsafeFromIntegral
    ) where

import Prelude hiding ( null )
import Data.Bits
import Data.Data


data BitSet a = BS {-# UNPACK #-} !Int {-# UNPACK #-} !Integer
                deriving (Eq, Ord, Data, Typeable)

instance (Enum a, Show a) => Show (BitSet a) where
    show (BS _ i :: BitSet a) = "fromList " ++ show (f 0 i)
        where f _ 0 = []
              f n x = if testBit x 0
                      then (toEnum n :: a) : f (n+1) (shiftR x 1)
                      else f (n+1) (shiftR x 1)

-- | The empty bit set.
empty :: BitSet a

-- | Is the bit set empty?
null :: BitSet a -> Bool

-- | /O(setBit on Integer)/ Insert an item into the bit set.
insert :: Enum a => a -> BitSet a -> BitSet a

-- | /O(n * setBit on Integer)/ Make a @BitSet@ from a list of items.
fromList :: Enum a => [a] -> BitSet a

-- | /O(clearBit on Integer)/ Delete an item from the bit set.
delete :: Enum a => a -> BitSet a -> BitSet a

-- | /O(testBit on Integer)/ Ask whether the item is in the bit set.
member :: Enum a => a -> BitSet a -> Bool

-- | /O(1)/ The number of elements in the bit set.
size :: BitSet a -> Int

-- | /O(1)/ Project a bit set to an integer.
toIntegral :: Integral b => BitSet a -> b

-- | /O(n)/ Make a bit set of type @BitSet a@ from an integer. This is unsafe
-- because it is not checked whether the bits set in the integer correspond to
-- values of type @a@. This is only useful as a more efficient alternative to
-- fromList.
unsafeFromIntegral :: Integral b => b -> BitSet a

-- * Implementation

{-# INLINE empty #-}
empty = BS 0 0

{-# INLINE null #-}
null (BS n _) = n == 0

{-# INLINE insert #-}
insert x (BS count i) = BS count' (setBit i e)
    where count' = if testBit i e then count else count+1
          e      = fromEnum x

fromList xs = BS (length xs) (foldl (\i x -> setBit i (fromEnum x)) 0 xs)

{-# INLINE delete #-}
delete x (BS count i) = BS count' (clearBit i e)
    where count' = if testBit i e then count-1 else count
          e      = fromEnum x

{-# INLINE member #-}
member x (BS _ i) = testBit i (fromEnum x)

{-# INLINE size #-}
size (BS count _) = count

{-# INLINE toIntegral #-}
toIntegral (BS _ i) = fromIntegral i

{-# INLINE unsafeFromIntegral #-}
unsafeFromIntegral x = let i = fromIntegral x in BS (count i) i
    where count 0 = 0
          count z | z `mod` 2 == 0 = 1 + count (shiftR z 1)
                  | otherwise = count (shiftR z 1)
