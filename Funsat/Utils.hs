{-# LANGUAGE PatternSignatures
            ,MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
            ,FlexibleContexts #-}

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


{-|

Generic utilities that happen to be used in the SAT solver.  In pretty much
every case, these functions will be useful for any number of manipulations,
and are not SAT-solver specific.

-}
module Funsat.Utils where

import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ( (>=>), forM_ )
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable hiding ( sequence_ )
import Data.List( foldl1' )
import Debug.Trace( trace )
import Prelude hiding ( sum, concatMap, elem, foldr, foldl, any, maximum )
import System.IO.Unsafe( unsafePerformIO )
import System.IO( hPutStr, stderr )
import qualified Data.Foldable as Fl
import qualified Data.List as List


{-# INLINE mytrace #-}
mytrace msg expr = unsafePerformIO $ do
    hPutStr stderr msg
    return expr

outputConflict fn g x = unsafePerformIO $ do writeFile fn g
                                             return x


-- | /O(1)/ Whether a list contains a single element.
isSingle :: [a] -> Bool
{-# INLINE isSingle #-}
isSingle [_] = True
isSingle _   = False

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


-- | Count the number of elements in the list that satisfy the predicate.
count :: (a -> Bool) -> [a] -> Int
count p = foldl' f 0
    where f x y | p y       = x + 1
                | otherwise = x

-- | /O(1)/ @argmin f x y@ is the argument whose image is least under @f@; if
-- the images are equal, returns the first.
argmin :: Ord b => (a -> b) -> a -> a -> a
argmin f x y = if f x <= f y then x else y

-- | /O(length xs)/ @argminimum f xs@ returns the value in @xs@ whose image
-- is least under @f@; if @xs@ is empty, throws an error.
argminimum :: Ord b => (a -> b) -> [a] -> a
argminimum f = foldl1' (argmin f)


-- | Show the value with trace, then return it.  Useful because you can wrap
-- it around any subexpression to print it when it is forced.
tracing :: (Show a) => a -> a
tracing x = trace (show x) x

-- | Returns a predicate which holds exactly when both of the given predicates
-- hold.
p .&&. q = \x -> p x && q x

