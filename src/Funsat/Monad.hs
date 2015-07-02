{-# LANGUAGE PolymorphicComponents
            ,MultiParamTypeClasses
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


{-|

The main SAT solver monad.  Embeds `ST'.  See type `SSTErrMonad', which stands
for ''State ST Error Monad''.

-}
module Funsat.Monad
    ( liftST
    , runSSTErrMonad
    , evalSSTErrMonad
    , SSTErrMonad )
    where
import Control.Monad.ST.Strict
import Control.Monad.State.Class
import Control.Monad.MonadST
import Control.Applicative (WrappedMonad)
import Control.Monad.Except
import Control.Applicative


instance MonadST s (SSTErrMonad e st s) where
    liftST = dpllST

-- | Perform an @ST@ action in the DPLL monad.
dpllST :: ST s a -> SSTErrMonad e st s a
{-# INLINE dpllST #-}
dpllST st = SSTErrMonad (\k s -> st >>= \x -> k x s)

-- | @runSSTErrMonad m s@ executes a `SSTErrMonad' action with initial state @s@
-- until an error occurs or a result is returned.
runSSTErrMonad :: SSTErrMonad e st s a -> (st -> ST s (Either e a, st))
runSSTErrMonad m = unSSTErrMonad m (\x s -> return (return x, s))

evalSSTErrMonad :: SSTErrMonad e st s a -> st -> ST s (Either e a)
evalSSTErrMonad m s = do (result, _) <- runSSTErrMonad m s
                         return result

-- | @SSTErrMonad e st s a@: the error type @e@, state type @st@, @ST@ thread
-- @s@ and result type @a@.
--
-- This is a monad embedding @ST@ and supporting error handling and state
-- threading.  It uses CPS to avoid checking `Left' and `Right' for every
-- `>>='; instead only checks on `catchError'. Idea adapted from
-- <http://haskell.org/haskellwiki/Performance/Monads>.
newtype SSTErrMonad e st s a =
    SSTErrMonad { unSSTErrMonad :: forall r. (a -> (st -> ST s (Either e r, st)))
                                -> (st -> ST s (Either e r, st)) }

instance Monad (SSTErrMonad e st s) where
    return x = SSTErrMonad ($ x)
    (>>=)    = bindSSTErrMonad

bindSSTErrMonad :: SSTErrMonad e st s a -> (a -> SSTErrMonad e st s b)
                -> SSTErrMonad e st s b
{-# INLINE bindSSTErrMonad #-}
bindSSTErrMonad m f =
    {-# SCC "bindSSTErrMonad" #-}
    SSTErrMonad (\k -> unSSTErrMonad m (\a -> unSSTErrMonad (f a) k))

instance MonadState st (SSTErrMonad e st s) where
    get    = SSTErrMonad (\k s -> k s s)
    put s' = SSTErrMonad (\k _ -> k () s')

instance MonadError e (SSTErrMonad e st s) where
    throwError err =            -- throw away continuation
        SSTErrMonad (\_ s -> return (Left err, s))
    catchError action handler = {-# SCC "catchErrorSSTErrMonad" #-} SSTErrMonad
        (\k s -> do (x, s') <- runSSTErrMonad action s
                    case x of
                      Left error -> unSSTErrMonad (handler error) k s'
                      Right result -> k result s')

instance Alternative (SSTErrMonad e st s) where
    empty = return undefined

instance MonadPlus (SSTErrMonad e st s) where
    mzero     = SSTErrMonad (\_ s -> return (Left undefined, s)) -- UMMMMM
    mplus m n = SSTErrMonad (\k s ->
                                 do (r, s') <- runSSTErrMonad m s
                                    case r of
                                      Left _ -> unSSTErrMonad n k s'
                                      Right x -> k x s')

-- Makes ghc happy
instance Applicative (SSTErrMonad e st s) where
    pure x = SSTErrMonad ($ x)
    mf <*> mx = do f <- mf
                   x <- mx
                   return (f x)
    mx *> my = do _ <- mx
                  y <- my
                  return y
    mx <* my = do x <- mx
                  _ <- my
                  return x

instance Functor (SSTErrMonad e st s) where
    fmap f ma = do x <- ma
                   return (f x)
    x <$ my = do _ <- my
                 return x
