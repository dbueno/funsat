-- | A /bit set/ maintains a record of members from a type that can be mapped
-- into (non-negative) @Int@s.  Supports insertion, deletion, size, and
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
    , delete
    , member
    , size
    ) where

import Prelude hiding ( null )
import Data.Bits


-- | The @Show@ instance kind of sucks.  It just shows the size paired with
-- the internal @Integer@ representation.  A good show would probably show all
-- the present hashes.
newtype BitSet a = BS { unBS :: (Int, Integer) }
    deriving (Eq)

instance Show (BitSet a) where
    show s = "BitSet " ++ show (unBS s)

-- | The empty bit set.
empty :: BitSet a

-- | Is the bit set empty?
null :: BitSet a -> Bool

-- | /O(setBit on Integer)/ Insert an item into the bit set.
insert :: Enum a => a -> BitSet a -> BitSet a

-- | /O(clearBit on Integer)/ Delete an item from the bit set.
delete :: Enum a => a -> BitSet a -> BitSet a

-- | /O(testBit on Integer)/ Ask whether the item is in the bit set.
member :: Enum a => a -> BitSet a -> Bool

-- | /O(1)/ The number of elements in the bit set.
size :: BitSet a -> Int


-- * Implementation

empty = BS (0, 0)

null (BS (n, _)) = n == 0

{-# INLINE insert #-}
insert x (BS (count, i)) = BS $ (count', setBit i e)
    where count' = if testBit i e then count else count+1
          e      = fromEnum x

{-# INLINE delete #-}
delete x (BS (count, i)) = BS $ (count', clearBit i e)
    where count' = if testBit i e then count-1 else count
          e      = fromEnum x

{-# INLINE member #-}
member x (BS (_, i)) = testBit i (fromEnum x)

{-# INLINE size #-}
size (BS (count, _)) = count
