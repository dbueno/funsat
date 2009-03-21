
-- Modify-in-place fibonacci heap.
module Data.FibHeapST where

import Control.Monad.ST
import Data.STRef

data Heap s k a = H
    { min       :: STRef s (Maybe (Info s k a))
    , size      :: STRef s Int  -- ^ Number of elements in the heap.
    , numMarked :: STRef s Int }

-- | Info kept for each node in the tree.
data Info s k a = Info
    { key    :: STRef s k
    , parent :: STRef s (Maybe (Info s k a))
    , child  :: STRef s (Maybe (Info s k a))
    , left   :: STRef s (Info s k a)
    , right  :: STRef s (Info s k a)
    , mark   :: STRef s Bool    -- ^ Has this node lost a child since the last
                                -- time it was made the child of another node?
    , datum  :: a }


splice :: Info s k a -> Info s k a -> ST s ()
splice n n' = do
    r <- readSTRef $ right n
    l  <- readSTRef $ left n
    writeSTRef (right n) n'
    writeSTRef (left n') n
    writeSTRef (left r) l
    writeSTRef (right l) r

remove node = do
    r <- readSTRef $ right node
    l <- readSTRef $ left node
    writeSTRef (right l) r
    writeSTRef (left r) l

    writeSTRef (right node) node
    writeSTRef (left node) node
        
