{-# LANGUAGE MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
 #-}


{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

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

