module Integration where

import Control.Monad (forM_, when)
import Data.Array.Unboxed (elems)
import Data.List (isSuffixOf, sort)
import Funsat.Circuit (input, problemCnf, runShared, toCNF)
import Funsat.Resolution (ResolutionTrace)
import Funsat.Solver (Solution(..), solve1, verify)
import Funsat.Types (CNF(..))
import System.Directory (listDirectory)
import System.FilePath ((</>))

import qualified Data.Set as Set
import qualified Funsat.Circuit as Circuit
import qualified Language.CNF.Parse.ParseDIMACS as ParseDIMACS

main :: IO ()
main = do
    regressionReportedCrash
    runCorpus "uf20" 1000 SatExpected "tests/problems/uf20"
    runCorpus "uf50" 1000 SatExpected "tests/problems/uf50"
    runCorpus "uuf50" 1000 UnsatExpected "tests/problems/uuf50"

data Expected = SatExpected | UnsatExpected

runCorpus :: String -> Int -> Expected -> FilePath -> IO ()
runCorpus label limit expected dir = do
    names <- sort `fmap` listDirectory dir
    let paths = take limit
              [dir </> name | name <- names, ".cnf" `isSuffixOf` name]
    forM_ paths $ \path -> do
        cnf <- parseCNF path
        let (solution, _, resolutionTrace) = solve1 cnf
        assertExpected expected path solution
        case verify solution resolutionTrace cnf of
          Nothing -> return ()
          Just err -> ioError . userError $
              path ++ ": verification failed: " ++ show err
    putStrLn $
        "Corpus " ++ label ++ ": " ++ show (length paths) ++ " cases passed"

regressionReportedCrash :: IO ()
regressionReportedCrash = do
    assertExpected SatExpected "reported CNF regression" solution1
    assertVerified "reported CNF regression" solution1 trace1 cnf
    assertExpected SatExpected "reported circuit regression" solution2
    assertVerified "reported circuit regression" solution2 trace2 circuitCnf
  where
    cnf =
        CNF
            { numVars = 6
            , numClauses = 11
            , clauses =
                Set.fromList
                    [ [-6, -5]
                    , [-5, -3, 2]
                    , [-5, 1]
                    , [-4, -3]
                    , [-2, 1]
                    , [-2, 3]
                    , [-2, 5]
                    , [-1, 2, 5]
                    , [1]
                    , [3, 4]
                    , [5, 6]
                    ]
            }
    (solution1, _, trace1) = solve1 cnf
    circuitCnf =
        problemCnf . toCNF . runShared $
            foldl1 Circuit.or
                [ foldl1 Circuit.and
                    [ Circuit.not (input (1 :: Integer))
                    , Circuit.not (input (2 :: Integer))
                    ]
                , Circuit.not (input (2 :: Integer))
                ]
    (solution2, _, trace2) = solve1 circuitCnf

assertExpected :: Expected -> FilePath -> Solution -> IO ()
assertExpected expected path solution =
    when (mismatch expected solution) $
        ioError . userError $
            path ++ ": expected " ++ expectedLabel expected
                ++ ", got " ++ show solution

mismatch :: Expected -> Solution -> Bool
mismatch SatExpected Sat{} = False
mismatch UnsatExpected Unsat{} = False
mismatch _ _ = True

expectedLabel :: Expected -> String
expectedLabel SatExpected = "satisfiable"
expectedLabel UnsatExpected = "unsatisfiable"

assertVerified :: FilePath -> Solution -> Maybe ResolutionTrace -> CNF -> IO ()
assertVerified _ Sat{} Nothing _ = return ()
assertVerified path solution resolutionTrace cnf =
    case verify solution resolutionTrace cnf of
      Nothing -> return ()
      Just err -> ioError . userError $
          path ++ ": verification failed: " ++ show err

parseCNF :: FilePath -> IO CNF
parseCNF path = do
    result <- ParseDIMACS.parseFile path
    case result of
      Left err -> error . show $ err
      Right c -> return . asCNF $ c

asCNF :: ParseDIMACS.CNF -> CNF
asCNF (ParseDIMACS.CNF v c is) =
    CNF
        { numVars = v
        , numClauses = c
        , clauses = Set.fromList . map (map fromIntegral . elems) $ is
        }
