module Data.IntMap.Adapter where

import Data.IntMap
import qualified Data.IntMap as IntMap

class Hash a where
    hash :: a -> Int

type Map a = IntMap a

empty = IntMap.empty

(!) m i = m IntMap.! hash i

lookup i m = IntMap.lookup (hash i) m