{-# LANGUAGE MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
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


-- | Idea from <http://haskell.org/pipermail/libraries/2003-September/001411.html>
module Control.Monad.MonadST where

import Control.Monad.ST
import Data.STRef

-- | A type class for monads that are able to perform `ST' actions.
class (Monad m) => MonadST s m | m -> s where
    liftST :: ST s a -> m a

instance MonadST s (Control.Monad.ST.ST s) where
    liftST = id

readSTRef :: MonadST s m => STRef s a -> m a
readSTRef = liftST . Data.STRef.readSTRef

writeSTRef :: MonadST s m => STRef s a -> a -> m ()
writeSTRef r x = liftST (Data.STRef.writeSTRef r x)

newSTRef :: MonadST s m => a -> m (STRef s a)
newSTRef = liftST . Data.STRef.newSTRef

modifySTRef :: MonadST s m => STRef s a -> (a -> a) -> m ()
modifySTRef r f = liftST (Data.STRef.modifySTRef r f)

