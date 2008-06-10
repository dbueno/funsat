{-# OPTIONS_GHC -fglasgow-exts #-}
module Properties where

{-
    This file is part of DPLLSat.

    DPLLSat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    DPLLSat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with DPLLSat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}

import Funsat.Solver hiding ((==>))

import Control.Monad (replicateM)
import Data.Array.Unboxed
import Data.BitSet (hash)
import Data.Bits
import Data.Foldable hiding (sequence_)
import Data.List (nub, splitAt, unfoldr, delete, sort, sortBy)
import Data.Maybe
import Data.Ord( comparing )
import Debug.Trace
import Funsat.Types
import Funsat.Utils( count, argmin )
import Language.CNF.Parse.ParseDIMACS( parseCNF )
import Prelude hiding ( or, and, all, any, elem, minimum, foldr, splitAt, concatMap
                      , sum, concat )
import System.Random
import Test.QuickCheck hiding (defaultConfig)
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Funsat.Resolution as Resolution
import qualified Test.QuickCheck as QC
import qualified Language.CNF.Parse.ParseDIMACS as ParseCNF


main :: IO ()
main = do
--   let s = solve1 prob1
--   case s of
--     Unsat -> return ()
--     Sat m -> if not (verifyBool m prob1)
--              then putStrLn (show (find (`isFalseUnder` m) prob1))
--              else return ()

      --setStdGen (mkStdGen 42)
      check config prop_randAssign
      check config prop_allIsTrueUnderA
      check config prop_noneIsFalseUnderA
      check config prop_noneIsUndefUnderA
      check config prop_negIsFalseUnder
      check config prop_negNotUndefUnder
      check config prop_outsideUndefUnder
      check config prop_clauseStatusUnderA
      check config prop_negDefNotUndefUnder
      check config prop_undefUnderImpliesNegUndef
      check config prop_litHash
      check config prop_varHash
      check config prop_count

      -- Add more tests above here.  Setting the rng keeps the SAT instances
      -- the same even if more tests are added above.  Reproducible results
      -- are important.
      setStdGen (mkStdGen 42)
      check solveConfig prop_solveCorrect

      setStdGen (mkStdGen 42)
      check resChkConfig prop_resolutionChecker

config = QC.defaultConfig { configMaxTest = 1000 }

-- Special configuration for the "solve this random instance" tests.
solveConfig = QC.defaultConfig { configMaxTest = 2000 }
resChkConfig = QC.defaultConfig{ configMaxTest = 1200 }

myConfigEvery testnum args = show testnum ++ ": " ++ show args ++ "\n\n"

-- * Tests
prop_solveCorrect (cnf :: CNF) =
    label "prop_solveCorrect" $
    trivial (numClauses cnf < 2 || numVars cnf < 2) $
    classify (numClauses cnf > 15 || numVars cnf > 10) "c>15, v>10" $
    classify (numClauses cnf > 30 || numVars cnf > 20) "c>30, v>20" $
    classify (numVars cnf > 20) "c>30, v>30" $
    case solve (defaultConfig cnf) cnf of
      (Sat m,_,_) -> label "SAT" $ verifyBool m cnf
      (Unsat _,_,rt) -> label "UNSAT" $
                        case Resolution.checkDepthFirst (fromJust rt) of
                          Left e ->
                                trace ("rt = " ++ show rt ++ "\n"
                                       ++ "Resolution checker error: " ++ show e)
                              $ False
                          Right _ -> True

prop_resolutionChecker (cnf :: UnsatCNF) =
    label "prop_resolutionChecker" $
    case solve1 (unUnsatCNF cnf) of
      (Sat _,_,_)    -> label "SAT" True
      (Unsat _,_,rt) -> label "UNSAT" $
          case Resolution.checkDepthFirst (fromJust rt) of
            Left e -> False
            Right unsatCore ->
                case solve1 ((unUnsatCNF cnf){ clauses = Set.fromList unsatCore}) of
                  (Sat _,_,_) -> False
                  (Unsat _,_,_) -> True

prop_allIsTrueUnderA (m :: IAssignment) =
    label "prop_allIsTrueUnderA"$
    allA (\i -> if i /= 0 then L i `isTrueUnder` m else True) m

prop_noneIsFalseUnderA (m :: IAssignment) =
    label "prop_noneIsFalseUnderA"$
    not $ anyA (\i -> if i /= 0 then L i `isFalseUnder` m else False) m

prop_noneIsUndefUnderA (m :: IAssignment) =
    label "prop_noneIsUndefUnderA"$
    not $ anyA (\i -> if i /= 0 then L i `isUndefUnder` m else False) m

prop_negIsFalseUnder (m :: IAssignment) =
    label "prop_negIsFalseUnder"$
    allA (\l -> if l /= 0 then negate (L l) `isFalseUnder` m else True) m

prop_negNotUndefUnder (m :: IAssignment) =
    label "prop_negNotUndefUnder"$
    allA (\l -> if l /= 0 then not (negate (L l) `isUndefUnder` m) else True) m

prop_outsideUndefUnder (l :: Lit) (m :: IAssignment) =
    label "prop_outsideUndefUnder"$
    trivial ((unVar . var) l > rangeSize (bounds m)) $
    inRange (bounds m) (var l) ==>
    trivial (m `contains` l || m `contains` negate l) $
    not (m `contains` l) && not (m `contains` (negate l)) ==>
    l `isUndefUnder` m

prop_negDefNotUndefUnder (l :: Lit) (m :: IAssignment) =
    label "prop_negDefNotUndefUnder" $
    inRange (bounds m) (var l) ==>
    m `contains` l || m `contains` (negate l) ==>
    l `isTrueUnder` m || negate l `isTrueUnder` m

prop_undefUnderImpliesNegUndef (l :: Lit) (m :: IAssignment) =
    label "prop_undefUnderImpliesNegUndef" $
    inRange (bounds m) (var l) ==>
    trivial (m `contains` l) $
    l `isUndefUnder` m ==> negate l `isUndefUnder` m
    

prop_clauseStatusUnderA (c :: Clause) (m :: IAssignment) =
    label "prop_clauseStatusUnderA" $
    classify expectTrueTest "expectTrue"$
    classify expectFalseTest "expectFalseTest"$
    classify expectUndefTest "expectUndefTest"$
    if expectTrueTest then c `isTrueUnder` m
    else if expectFalseTest then c `isFalseUnder` m
    else c `isUndefUnder` m
        where
          expectTrueTest = not . null $ c `List.intersect` (map L $ elems m)
          expectFalseTest = all (`isFalseUnder` m) c
          expectUndefTest = not expectTrueTest && not expectFalseTest

-- Verify assignments generated are sane, i.e. no assignment contains an
-- element and its negation.
prop_randAssign (a :: IAssignment) =
    label "randAssign"$
    not $ anyA (\l -> if l /= 0 then a `contains` (negate $ L l) else False) a

-- unitPropFar should stop only if it can't propagate anymore.
-- prop_unitPropFarthest (m :: Assignment) (cnf :: CNF) =
--     label "prop_unitPropFarthest"$
--     case unitPropFar m cnf of
--       Nothing -> label "no propagation" True
--       Just m' -> label "propagated" $ not (anyUnit m' cnf)

-- Unit propagation may only add to the given assignment.
-- prop_unitPropOnlyAdds (m :: Assignment) (cnf :: CNF) =
--     label "prop_unitPropOnlyAdds"$
--     case unitPropFar m cnf of
--       Nothing -> label "no propagation" True
--       Just m' -> label "propagated" $ all (\l -> elem l m') m

-- Make sure the bit set will work.

prop_litHash (k :: Lit) (l :: Lit) =
    label "prop_litHash" $
    hash k == hash l <==> k == l

prop_varHash (k :: Var) l =
    label "prop_varHash" $
    hash k == hash l <==> k == l


(<==>) = iff
infixl 3 <==>


-- newtype WPTest s = WPTest (WatchedPair s)

-- instance Arbitrary (WPTest s) where
--     arbitrary = sized sizedWPTest
--         where sizedWPTest n = do
--                 [lit1, lit2] <- 2 `uniqElts` 1
--                 clause :: Clause <- arbitrary
--                 return $ runST $
--                          do r <- newSTRef (lit1, lit2)
--                             return (r, lit1 : lit2 : clause)

newtype Nat = Nat { unNat :: Int }
    deriving (Eq, Ord)
instance Show Nat where
    show (Nat i) = "Nat " ++ show i
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

instance Arbitrary Nat where
    arbitrary = sized $ \n -> do i <- choose (0, n)
                                 return (fromIntegral i)


-- sanity checking for Arbitrary Nat instance.
prop_nat (xs :: [Nat]) = trivial (null xs) $ sum xs >= 0
prop_nat1 (xs :: [Nat]) = trivial (null xs) $ unNat (sum xs) == sum (map unNat xs)

prop_count p xs =
    label "prop_count" $
    count p xs == length (filter p xs)
        where _types = xs :: [Int]

prop_argmin f x y =
    label "prop_argmin" $
    f x /= f y ==>
      argmin f x y == m
  where m = if f x < f y then x else y

instance Show (a -> b) where
    show = const "<fcn>"



------------------------------------------------------------------------------
-- * Helpers
------------------------------------------------------------------------------



allA :: (IArray a e, Ix i) => (e -> Bool) -> a i e -> Bool
allA p a = all (p . (a !)) (range . bounds $ a)

anyA :: (IArray a e, Ix i) => (e -> Bool) -> a i e -> Bool
anyA p a = any (p . (a !)) (range . bounds $ a)

_findA :: (IArray a e, Ix i) => (e -> Bool) -> a i e -> Maybe e
_findA p a = (a !) `fmap` find (p . (a !)) (range . bounds $ a)


-- Generate exactly n distinct, random things from given enum, starting at
-- element given.  Obviously only really works for infinite enumerations.
uniqElts :: (Enum a) => Int -> a -> Gen [a]
uniqElts n x =
    do is <- return [x..]
       choices <-
           sequence $ map
                      (\i -> do {b <- oneof [return True, return False];
                                 return $ if b then Just i else Nothing})
                      is
       return $ take n $ catMaybes choices

-- Send this as a patch for quickcheck, maybe.
iff :: Bool -> Bool -> Property
first `iff` second =
    classify first "first" $
    classify (not first) "not first" $
    classify second "second" $
    classify (not second) "not second" $
    if first then second
    else not second
    && if second then first
       else not first


fromRight (Right x) = x
fromRight (Left _) = error "fromRight: Left"


_intAssignment :: Int -> Integer -> [Lit]
_intAssignment n i = map nthBitLit [0..n-1]
    -- nth bit of i as a literal
    where nthBitLit n = toLit (n + 1) $ i `testBit` n
          toLit n True  = L n
          toLit n False = negate $ L n
                         


_powerset       :: [a] -> [[a]]
_powerset []     = [[]]
_powerset (x:xs) = xss /\/ map (x:) xss
    where
      xss = _powerset xs

      (/\/)        :: [a] -> [a] -> [a]
      []     /\/ ys = ys
      (x:xs) /\/ ys = x : (ys /\/ xs)


------------------------------------------------------------------------------
-- * Generators
------------------------------------------------------------------------------

instance Arbitrary Var where
    arbitrary = sized $ \n -> V `fmap` choose (1, n)
instance Arbitrary Lit where
    arbitrary = sized $ sizedLit

-- Generates assignment that never has a subset {l, -l}.
instance Arbitrary IAssignment where
    arbitrary = sized assign'
        where 
          assign' n = do lits :: [Lit] <- vector n
                         return $ array (V 1, V n) $ map (\i -> (var i, unLit i))
                                                     (nub lits)

instance Arbitrary CNF where
    arbitrary = sized (genRandom3SAT 3.0)

sizedLit n = do
  v <- choose (1, n)
  t <- oneof [return id, return negate]
  return $ L (t v)

-- Generate a random 3SAT problem with the given ratio of clauses/variable.
--
-- Current research suggests:
--
--  * ~ 4.3: hardest instances
--  * < 4.3: SAT & easy
--  * > 4.3: UNSAT & easy
genRandom3SAT :: Double -> Int -> Gen CNF
genRandom3SAT clausesPerVar n =
    do let nClauses = ceiling (fromIntegral nVars * clausesPerVar)
       clauseList <- replicateM nClauses arbClause
       return $ CNF { numVars    = nVars
                    , numClauses = nClauses
                    , clauses    = Set.fromList clauseList }
  where 
    nVars = n `div` 3
    arbClause :: Gen Clause
    arbClause = do
      a <- sizedLit nVars
      b <- sizedLit nVars
      c <- sizedLit nVars
      return [a,b,c]


windows :: Int -> [a] -> [[a]]
windows n xs = if length xs < n
               then []
               else take n xs : windows n (drop n xs)

permute :: [a] -> Gen [a]
permute [] = return []
permute xs = choose (0, length xs - 1) >>= \idx ->
             case splitAt idx xs of
               (pfx, x:xs') -> do perm <- permute $ pfx ++ xs'
                                  return $ x : perm
               _            -> error "permute: bug"


newtype UnsatCNF = UnsatCNF { unUnsatCNF :: CNF } deriving (Show)
instance Arbitrary UnsatCNF where
    arbitrary = do
        f <- sized (genRandom3SAT 5.19)
        return (UnsatCNF f)




------------------------------------------------------------------------------
-- ** Simplification
------------------------------------------------------------------------------

class WellFoundedSimplifier a where
    -- | If the argument can be made simpler, a list of one-step simpler
    -- objects.  Only in cases where there are multiple "dimensions" to
    -- simplify should the returned list have length more than 1.  Otherwise
    -- returns the empty list.
    simplify :: a -> [a]

instance WellFoundedSimplifier a => WellFoundedSimplifier [a] where
    simplify []     = []
    simplify (x:xs) = case simplify x of
                        [] -> [xs]
                        x's-> map (:xs) x's

instance WellFoundedSimplifier () where
    simplify () = []

instance WellFoundedSimplifier Bool where
    simplify True = [False]
    simplify False = []

instance WellFoundedSimplifier Int where
  simplify i | i == 0 = []
             | i > 0  = [i-1]
             | i < 0  = [i+1]

-- Assign the highest variable and reduce the number of variables.
instance WellFoundedSimplifier CNF where
    simplify f
        | numVars f <= 1 = []
        | numVars f > 1 = [ f{ numVars    = numVars f - 1
                             , clauses    = clauses'
                             , numClauses = Set.size clauses' }
--                           , f{ clauses    = Set.deleteMax (clauses f)
--                              , numClauses = numClauses f - 1 }
                          ]
      where
        clauses' = foldl' assignVar Set.empty (clauses f)
        pos = L (numVars f)
        neg = negate pos
        assignVar outClauses clause =
            let clause' = neg `delete` clause
            in if pos `elem` clause || null clause' then outClauses
               else clause' `Set.insert` outClauses


simplifications :: WellFoundedSimplifier a => a -> [a]
simplifications a = concat $ unfoldr (\ xs -> let r = concatMap simplify xs
                                              in if null r then Nothing
                                                 else Just (r, r))
                                     [a]

-- Returns smallest CNF simplification that also gives erroneous output.
minimalError :: CNF -> CNF
minimalError f = lastST f satAndWrong (simplifications f)
    where satAndWrong f_inner =
              trace (show (numVars f_inner) ++ "/" ++ show (numClauses f_inner)) $
              case solve1 f_inner of
                (Unsat _,_,_)        -> False
                (Sat assignment,_,_) -> not (verifyBool assignment f_inner)

-- last (takeWhile p xs) in the common case.
-- mnemonic: "last Such That"
lastST def _ []     = def
lastST def p (x:xs) = if p x then lastST x p xs else def

prop_lastST (x :: Int) =
    if not (null xs) && xa > 3 then
        classify True "nontrivial" $
        last (takeWhile p xs) == lastST undefined p xs
    else True `trivial` True
  where p  = (> xa `div` 2)
        xs = simplifications xa
        xa = abs x


getCNF :: Int -> IO CNF
getCNF maxVars = do g <- newStdGen
                    return (generate (maxVars * 3) g arbitrary)

prob :: IO ParseCNF.CNF
prob = do let file = "./tests/problems/uf20/uf20-0119.cnf"
          s <- readFile file
          return $ parseCNF file s


-- | Convert parsed CNF to internal representation.
asCNF :: ParseCNF.CNF -> CNF
asCNF (ParseCNF.CNF v c is) =
    CNF {numVars = v
        ,numClauses = c
        ,clauses = Set.fromList . map (map fromIntegral) $ is}


-- import qualified Data.ByteString.Char8 as B

-- hStrictGetContents :: Handle -> IO String
-- hStrictGetContents h = do
--    bs <- B.hGetContents h
--    hClose h -- not sure if this is required; ByteString documentation isn't clear.
--    return $ B.unpack bs -- lazy unpack into String


verifyBool :: IAssignment -> CNF -> Bool
verifyBool m problem = isNothing $ verify m problem

