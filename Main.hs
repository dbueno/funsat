{-# OPTIONS -cpp #-}

module Main where

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

import Control.Monad ( when, forM_ )
import Data.Foldable ( fold, toList, elem )
import Data.List ( intercalate )
import Data.Monoid
import Data.Set ( Set )
import DPLLSat( solve
              , DPLLConfig(..)
              , defaultConfig
              , CNF
              , GenCNF(..)
              , Solution(..)
              , verify
              , NonStupidString(..)
              , statTable )
import Prelude hiding ( elem )
import System.Console.GetOpt
import System.Environment ( getArgs )
import System.Exit ( ExitCode(..), exitWith )
import System.Random ( mkStdGen )
import Data.Time.Clock
import qualified Data.Set as Set
import qualified Language.CNF.Parse.ParseDIMACS as ParseCNF
import qualified Text.Tabular as Tabular


#ifdef TESTING
import qualified Properties
#endif

data Feature = WatchedLiterals
             | ClauseLearning
             | Restarts
             | VSIDS
               deriving (Eq, Ord)
instance Show Feature where
    show WatchedLiterals = "watched literals"
    show ClauseLearning  = "conflict clause learning"
    show Restarts        = "restarts"
    show VSIDS           = "dynamic variable ordering"

allFeatures :: Set Feature
allFeatures = Set.fromList [WatchedLiterals, ClauseLearning, Restarts, VSIDS]


validOptions :: [OptDescr RunOptions]
validOptions =
    [ Option [] ["no-clause-learning"] (NoArg $ disableF ClauseLearning)
             "Use naivest clause learning."
    , Option [] ["no-watched-literals"] (NoArg $ disableF WatchedLiterals)
             "Just traverse the formula to find unit clauses."
    , Option [] ["no-vsids"] (NoArg $ disableF VSIDS)
             "Use static variable ordering."
    , Option [] ["no-restarts"] (NoArg $ disableF Restarts)
             "Never restart."
    , Option [] ["verify"] (NoArg RunTests)
             "Run unit tests."
    , Option [] ["print-features"] (NoArg (PrintFeatures Set.empty))
             "Print the optimisations the SAT solver supports." ]

disableF :: Feature -> RunOptions
disableF = Disable . Set.singleton

data RunOptions = Disable (Set Feature)       -- disable certain features
                | RunTests                    -- run unit tests
                | PrintFeatures (Set Feature) -- disable certain features
-- Combines features, choosing only RunTests and PrintFeatures if present,
-- otherwise combining sets of features to disable.
instance Monoid RunOptions where
    mempty = Disable Set.empty
    mappend (PrintFeatures f) (PrintFeatures f') = PrintFeatures (f `Set.union` f')
    mappend (PrintFeatures f) (Disable f') = PrintFeatures (f `Set.union` f')
    mappend o@(PrintFeatures _) _ = o
    mappend o@RunTests _ = o
    mappend (Disable s) (Disable s') = Disable (s `Set.union` s')
    mappend (Disable _) o = o   -- non-feature selection options override

parseOptions :: [String] -> IO (RunOptions, [FilePath])
parseOptions args = do
    let (runoptionss, filepaths, errors) = getOpt RequireOrder validOptions args
    when (not (null errors)) $ do { mapM_ putStr errors ;
                                    putStrLn (usageInfo usageHeader validOptions) ;
                                    exitWith (ExitFailure 1) }
    return $ (fold runoptionss, filepaths)

main :: IO ()
main = do
    (opts, files) <- getArgs >>= parseOptions
    case opts of
#ifdef TESTING
      RunTests -> Properties.main
#endif
      PrintFeatures disabled ->
          putStrLn $ intercalate ", " $ map show $
                     toList (allFeatures Set.\\ disabled)
      Disable features -> do
        putStr "Enabled features: "
        putStrLn $ intercalate ", " $ map show $
                   toList (allFeatures Set.\\ features)
        forM_ files $ \path -> readFile path >>= parseAndSolve path
         where
           parseAndSolve path contents = do
              let cnf = asCNF $ ParseCNF.parseCNF path contents
              putStrLn $ show (numVars cnf) ++ " variables, "
                         ++ show (numClauses cnf) ++ " clauses"
              Set.map seqList (clauses cnf)
                `seq` putStrLn ("Solving " ++ path ++ "...")
              startingTime <- getCurrentTime
              let cfg =
                    (defaultConfig cnf)
                    { configUseVSIDS = not $ VSIDS `elem` features
                    , configUseWatchedLiterals = not $ WatchedLiterals `elem` features
                    , configUseRestarts = not $ Restarts `elem` features }
                  (solution, stats) = solve cfg (mkStdGen 1) cnf
              endingTime <- solution `seq` getCurrentTime
              print solution
              print $ statTable stats `Tabular.combine`
                      Tabular.mkTable
                       [[ Stupid "Real time "
                        , Stupid $ show (diffUTCTime endingTime startingTime)]]
              putStrLn "Verifying..."
              case solution of
                Sat m -> case verify m cnf of
                           Just problemClauses ->
                             do putStrLn "VERIFICATION ERROR!"
                                print problemClauses
                           Nothing -> return ()
#ifdef TESTING
--                               putStrLn $
--                                 "Minimal erroneous CNF:\n"
--                                 ++ show (Properties.minimalError cnf)
#endif TESTING
                Unsat -> return ()


usageHeader = "Usage: dsat [options] <cnf-filename> ... <cnf-filename>"

seqList l@[] = l
seqList l@(x:xs) = x `seq` seqList xs `seq` l


-- | Convert parsed CNF to internal representation.
asCNF :: ParseCNF.CNF -> CNF
asCNF (ParseCNF.CNF v c is) =
    CNF { numVars = v
        , numClauses = c
        , clauses = Set.fromList . map (map fromIntegral) $ is }

