-- | A /bit set/ maintains a record of members from a type that can be mapped
-- into (non-negative) @Int@s.  Supports insertion, deletion, size, and
-- membership testing, and is completely pure (functional).
--
-- To use this library, simply supply a `Hash' instance for your data type.
-- (See the `Hash' class for the relevant laws your instance must obey.)  Each
-- operation requires at most one call to `hash'.  It is important that the
-- values you intend to keep track of start from 0 and go up.  A value which
-- `hash'es to @n@ corresponds to bit location @n@ in an @Integer@, and thus
-- requires that @Integer@ to have at least @n@ bits.  Don't shoot yourself in
-- the foot by `hash'ing to big @Int@s.
--
-- The implementation is quite simple: we rely on the @Bits Integer@ instance
-- from @Data.Bits@.  An advantage of this library over simply using that
-- @Bits@ instance is the phantom type parameter used in the `BitSet' type.
-- The interface we expose ensures client code will not typecheck if it
-- confuses two bit sets intended to keep track of different types.
module Data.BitSet
    ( Hash(..)
    , BitSet
    , empty
    , null
    , insert
    , delete
    , member
    , size
    ) where

import Prelude hiding ( null )
import Data.Bits


-- | Map a value to an non-negative @Int@.
--
-- For the implementation to give reliable results, it must be that if @hash x
-- == hash y@, @x@ and @y@ are equivalent under the relevant relation used in
-- the client code.  (We don't depend on equality, but the client code will
-- certainly want to use the above sort of inference.)
--
-- In fact, if the relevant relation is @==@, the following quickcheck
-- test should pass, for arbitrary @x@ and @y@ of type @a@:
--
-- @prop_hash x y =
--     if hash x == hash y then x == y
--     else x /= y
--     && if x == y then hash x == hash y
--        else hash x /= hash y@
class Hash a where
    hash :: a -> Int

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
insert :: Hash a => a -> BitSet a -> BitSet a

-- | /O(clearBit on Integer)/ Delete an item from the bit set.
delete :: Hash a => a -> BitSet a -> BitSet a

-- | /O(testBit on Integer)/ Ask whether the item is in the bit set.
member :: Hash a => a -> BitSet a -> Bool

-- | /O(1)/ The number of elements in the bit set.
size :: BitSet a -> Int


-- * Implementation

empty = BS (0, 0)

null (BS (n, _)) = n == 0

{-# INLINE insert #-}
insert x s@(BS (count, i)) = BS $ (count', setBit i h)
    where count' = if h `memHash` s then count else count+1
          h      = hash x

{-# INLINE delete #-}
delete x s@(BS (count, i)) = BS $ (count', clearBit i h)
    where count' = if h `memHash` s then count-1 else count
          h      = hash x

{-# INLINE member #-}
member x s = hash x `memHash` s
memHash :: Int -> BitSet a -> Bool
{-# INLINE memHash #-}
memHash h (BS (_, i)) = testBit i h

{-# INLINE size #-}
size (BS (count, _)) = count

-- * Default instances

instance Hash Int where
    hash = id

instance Hash Integer where
    hash = fromIntegral

-- Needs UndecidableInstances?
-- instance Integral a => Hash a where
--     hash = fromIntegral

    
