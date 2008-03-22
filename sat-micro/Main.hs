module Main where

import Control.Monad
import Data.List (nub)
import SatMicro
import System.Environment (getArgs)
import System.Exit
import qualified Language.CNF.Parse.ParseDIMACS as ParseCNF


usage :: String
usage = "Usage:\nsat-micro <cnf-filename>"

-- | Run the SAT solver on the CNF file given as an argument.
main :: IO ()
main = do
    args <- getArgs
    case args of
      [] -> putStrLn usage
      path:_ -> readFile path >>= parseAndSolve
         where
           parseAndSolve contents =
              let cnf = asCnf $ ParseCNF.parseCNF path contents
              in do putStrLn ("Solving " ++ path ++ "...")
                    let result = dpll cnf
                    when (not (verifyResult result cnf)) $ do
                      print "VERIFICATION ERROR"
                      exitWith (ExitFailure 1)
                    print result

-- | Parse CNF file into internal representation.
asCnf :: ParseCNF.CNF -> CNF
asCnf (ParseCNF.CNF _ _ is) = map (nub . map fromIntegral) $ is