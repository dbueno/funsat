{-# LANGUAGE PolymorphicComponents
            ,MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
 #-}

{-| The main SAT solver monad.  Embeds `ST'.  See type `DPLLMonad'.

Most of the work done is in the form of `DPLLMonad' actions. -}
module DPLL.Monad where

import Control.Monad.Error hiding ((>=>), forM_)
import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Control.Monad.MonadST


instance MonadST s (DPLLMonad e st s) where
    liftST = dpllST

-- | Perform an @ST@ action in the DPLL monad.
dpllST :: ST s a -> DPLLMonad e st s a
{-# INLINE dpllST #-}
dpllST st = DPLLMonad (\k s -> st >>= \x -> k x s)

-- | @runDPLLMonad m s@ executes a `DPLLMonad' action with initial state @s@
-- until an error occurs or a result is returned.
runDPLLMonad :: (Error e) => DPLLMonad e st s a -> (st -> ST s (Either e a, st))
runDPLLMonad m = unDPLLMonad m (\x s -> return (return x, s))

execDPLLMonad :: (Error e) => DPLLMonad e st s a -> st -> ST s (Either e a)
execDPLLMonad m s = do (result, _) <- runDPLLMonad m s
                       return result

-- | @DPLLMonad e st s a@: the error type @e@, state type @st@, @ST@ thread
-- @s@ and result type @a@.
--
-- This is a monad embedding @ST@ and supporting error handling and state
-- threading.  It uses CPS to avoid checking `Left' and `Right' for every
-- `>>='; instead only checks on `catchError'. Idea adapted from
-- <http://haskell.org/haskellwiki/Performance/Monads>.
newtype DPLLMonad e st s a =
    DPLLMonad { unDPLLMonad :: forall r. (a -> (st -> ST s (Either e r, st)))
                              -> (st -> ST s (Either e r, st)) }

instance Monad (DPLLMonad e st s) where
    return x = DPLLMonad ($ x)
    m >>= f  = DPLLMonad (\k -> unDPLLMonad m (\a -> unDPLLMonad (f a) k))

instance MonadState st (DPLLMonad e st s) where
    get = DPLLMonad (\k s -> k s s)
    put s' = DPLLMonad (\k _ -> k () s')

instance (Error e) => MonadError e (DPLLMonad e st s) where
    throwError err =            -- throw away continuation
        DPLLMonad (\_ s -> return (Left err, s))
    catchError action handler = DPLLMonad
        (\k s -> do (x, s') <- runDPLLMonad action s
                    case x of
                      Left error -> unDPLLMonad (handler error) k s'
                      Right result -> k result s')
