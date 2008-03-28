module Data.DLList where

import Control.Monad.Fix
import Control.Monad.ST
import Data.STRef
import Data.SyntaxSugar

data Node s a = Node { prev :: STRef s (Node s a)
                     , elt  :: STRef s a
                     , next :: STRef s (Node s a) }

-- | A Node pointing only to inself.
singleton :: a -> ST s (Node s a)
singleton x = mdo r  <- ref n
                  rx <- ref x
                  n  <- return $ Node r rx r
                  return n


splice :: Node s a -> Node s a -> ST s ()
splice n n' = do
  right <- val (next n)
  left  <- val (prev n')
  next n =: n'
  prev n' =: n
  prev right =: left
  next left  =: right

remove :: Node s a -> ST s ()
remove n = do
  right <- val (next n)
  left  <- val (prev n)
  next left  =: right
  prev right =: left
  -- make returned node only point to self
  next n =: n
  prev n =: n