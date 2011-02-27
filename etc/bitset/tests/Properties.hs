module Properties where

import Control.Monad( liftM )
import Prelude hiding ( null )
import Data.BitSet
import Data.Foldable ( foldl' )
import Data.List ( nub )
import Test.QuickCheck
import System.IO

import qualified Data.List as List



main :: IO ()
main = do
  dbgMsg "prop_size: " >> quickCheckWith myargs prop_size
  dbgMsg "prop_size_insert: " >> quickCheckWith myargs prop_size_insert
  dbgMsg "prop_size_delete: " >> quickCheckWith myargs prop_size_delete
  dbgMsg "prop_insert: " >> quickCheckWith myargs prop_insert
  dbgMsg "prop_delete: " >> quickCheckWith myargs prop_delete
  dbgMsg "prop_insDelIdempotent: " >> quickCheckWith myargs prop_insDelIdempotent
  dbgMsg "prop_delDelIdempotent: " >> quickCheckWith myargs prop_delDelIdempotent
  dbgMsg "prop_insInsIdempotent: " >> quickCheckWith myargs prop_insInsIdempotent
  dbgMsg "prop_extensional: " >> quickCheckWith myargs prop_extensional
  dbgMsg "prop_fromList: " >> quickCheckWith myargs prop_fromList
  dbgMsg "prop_empty: " >> quickCheckWith myargs prop_empty
  dbgMsg "prop_integral: " >> quickCheckWith (myargs{ maxSize = 40 }) prop_integral

dbgMsg = hPutStr stderr

myargs = stdArgs{ maxSize = 64 }

-- * Quickcheck properties

trivial test = classify test "trivial"

prop_size xs =
    trivial (List.null uxs) $
    length uxs == size (foldr insert empty uxs)
        where uxs = nub (map abs xs) :: [Int]

prop_size_insert x s =
    trivial (null s) $
    if xa `member` s then size s == size s'
    else size s + 1 == size s'
  where s' = insert xa s
        xa = abs x :: Int

prop_size_delete x s =
    trivial (null s) $
    if xa `member` s then size s - 1 == size s'
    else size s == size s'
  where s' = delete xa s
        xa = abs x :: Int

prop_insert x s = xa `member` insert xa s
    where xa = abs x :: Int

prop_delete x s = not $ xa `member` delete xa s
    where xa = abs x :: Int

prop_insDelIdempotent x s =
    classify (not (xa `member` s)) "passed guard" $
    not (xa `member` s) ==>
    s == (delete xa . insert xa) s
  where xa = abs x :: Int

prop_delDelIdempotent x s =
    classify (xa `member` s) "x in s" $
    classify (not (xa `member` s)) "x not in s" $
    delete xa s == (delete xa . delete xa $ s)
  where xa = abs x :: Int

prop_insInsIdempotent x s = insert xa s == (insert xa . insert xa) s
    where xa = abs x :: Int

prop_extensional xs = and $ map (`member` s) xsa
    where s   = foldr insert empty xsa
          xsa = map abs xs :: [Int]

prop_fromList xs = all (`member` s) xsa
    where s   = fromList xsa
          xsa = map abs xs :: [Int]

prop_empty x = not $ xa `member` empty
    where xa = abs x :: Int

prop_integral x s = trivial (null s) $ xa `member` reconstructed
  where reconstructed = unsafeFromIntegral (toIntegral xs)
        xa = abs x :: Int
        xs = xa `insert` s



instance (Arbitrary a, Enum a) => Arbitrary (BitSet a) where
    arbitrary = sized $ liftM fromList . vector
