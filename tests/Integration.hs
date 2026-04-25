module Integration where

import Control.Monad (forM_, when)
import Data.Array.Unboxed (elems)
import Data.List (isSuffixOf, sort)
import Funsat.Solver (Solution(..), solve1, verify)
import Funsat.Types (CNF(..))
import System.Directory (listDirectory)
import System.FilePath ((</>))

import qualified Data.Set as Set
import qualified Language.CNF.Parse.ParseDIMACS as ParseDIMACS

main :: IO ()
main = do
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
