{-# OPTIONS_GHC -fglasgow-exts #-}
module Properties where

import Prelude hiding (sum, all, elem, min, maximum, minimum)
import Data.FibHeap
import Data.List(nub)
import Data.Foldable
import Data.Maybe ( fromJust )
import Test.QuickCheck
import qualified Data.FibHeap as H

#if 0

data T = forall a. Testable a => T a
config :: Config
config = defaultConfig{ configMaxTest = 1000 }
-- Run tests.
qc :: IO ()
qc = do _results <- mapM mycheck tests
        return ()
  where
    tests =
        [ T (label "insert updates size" prop_insert_size)
        , T (label "insert updates min" prop_insert_min)
        , T (label "decrease key to min" prop_decreaseKey)
        ]
mycheck (T t) = check config t

-- * Fibonacci heap tests



newtype Nat = Nat { unNat :: Int }
    deriving (Eq, Show, Ord)
instance Num Nat where
    (Nat x) + (Nat y) = Nat (x + y)
    (Nat x) - (Nat y) | x >= y = Nat (x - y)
                      | x < y  = error "Nat: subtraction out of range"
    (Nat x) * (Nat y) = Nat (x * y)
    abs = id
    signum (Nat n) | n == 0 = 0
                   | n > 0  = 1
                   | n < 0  = error "Nat: signum of negative number"
    fromInteger n | n >= 0 = Nat (fromInteger n)
                  | n < 0  = error "Negative natural literal found"

data MinNatPolicy
instance HeapPolicy MinNatPolicy Nat where
    heapMin = 0
    heapCompare _ (Nat x) (Nat y) = compare x y

instance Arbitrary Nat where
    arbitrary = sized $ \n -> do i <- choose (0, n)
                                 return (fromIntegral i)

type TestHeap = Heap MinNatPolicy Nat Nat

emptyNatHeap :: TestHeap
emptyNatHeap = H.empty

-- sanity checking for Arbitrary Nat instance.
prop_nat (xs :: [Nat]) = trivial (null xs) $ sum xs >= 0
prop_nat1 (xs :: [Nat]) = trivial (null xs) $ unNat (sum xs) == sum (map unNat xs)


prop_insert_size (xs :: [Nat]) =
    length xs == H.size (foldl' insertWithKey emptyNatHeap xs)

insertWithKey h n = H.insert (n, n) h

prop_insert_min (xsIn :: [Nat]) =
    trivial (null xs) $
    not (null xs) ==> minimum xsIn == minElt
  where minElt = datum . focusElement . min $
                 foldl' insertWithKey emptyNatHeap xs
        xs = nub xsIn

prop_decreaseKey (xsIn :: [Nat]) =
    trivial (null xs) $
    not (null xs) ==>
      minimum xsIn == (key . focusElement . min) h
  where h'  = decreaseKey h (min h) 0
        h   = foldl' insertWithKey emptyNatHeap xs
        xs  = nub xsIn
        maxElt = maximum xs
        maxEltInfo = Info { key   = maxElt
                          , mark  = False
                          , datum = maxElt }
        


------------------------------------------------------------------------------


instance Show (a -> b) where
    show = const "<function>"

#endif
