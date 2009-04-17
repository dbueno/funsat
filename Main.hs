{-# OPTIONS -cpp #-}

module Main where

{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}

import Control.Monad( when, forM_ )
import Data.Array.Unboxed( elems )
import Data.Foldable( fold, toList, elem )
import Data.List( intercalate )
import Data.Monoid
import Data.Set( Set )
import Funsat.Solver
    ( solve
    , verify
    , DPLLConfig(..)
    , defaultConfig
    , ShowWrapped(..)
    , statTable )
import Funsat.Types( CNF(..) )
import Prelude hiding ( elem )
import System.Console.GetOpt
import System.Environment( getArgs )
import System.Exit( ExitCode(..), exitWith )
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
             | ResolutionChecker
             | UnsatCoreGeneration
               deriving (Eq, Ord)
instance Show Feature where
    show WatchedLiterals = "watched literals"
    show ClauseLearning  = "conflict clause learning"
    show Restarts        = "restarts"
    show VSIDS           = "dynamic variable ordering"
    show ResolutionChecker = "resolution UNSAT checker"
    show UnsatCoreGeneration = "UNSAT core generation"

allFeatures :: Set Feature
allFeatures = Set.fromList [WatchedLiterals, ClauseLearning, Restarts, VSIDS
                           ,ResolutionChecker, UnsatCoreGeneration]


validOptions :: [OptDescr RunOptions]
validOptions =
    [ Option [] ["no-vsids"] (NoArg $ disableF VSIDS)
             "Use static variable ordering."
    , Option [] ["no-restarts"] (NoArg $ disableF Restarts)
             "Never restart."
    , Option [] ["verify"] (NoArg RunTests)
             "Run quickcheck properties and unit tests."
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
        forM_ files $ parseAndSolve
         where
           parseAndSolve path = do
              cnf <- parseCNF path
              putStrLn $ show (numVars cnf) ++ " variables, "
                         ++ show (numClauses cnf) ++ " clauses"
              Set.map seqList (clauses cnf)
                `seq` putStrLn ("Solving " ++ path ++ "...")
              startingTime <- getCurrentTime
              let cfg =
                    (defaultConfig cnf)
                    { configUseVSIDS = not $ VSIDS `elem` features
                    , configUseRestarts = not $ Restarts `elem` features }
                  (solution, stats, rt) = solve cfg cnf
              endingTime <- solution `seq` getCurrentTime
              print solution
              print $ statTable stats `Tabular.combine`
                      Tabular.mkTable
                       [[ WrapString "Real time "
                        , WrapString $ show (diffUTCTime endingTime startingTime)]]
              putStr "Verifying solution..."
              case verify solution rt cnf of
                Just errorWitness ->
                    do putStrLn "\n--> VERIFICATION ERROR!"
                       print errorWitness
                Nothing -> putStrLn "succeeded."


usageHeader = "Usage: funsat [options] <cnf-filename> ... <cnf-filename>"

seqList l@[] = l
seqList l@(x:xs) = x `seq` seqList xs `seq` l

parseCNF :: FilePath -> IO CNF
parseCNF path = do
    result <- ParseCNF.parseFile path
    case result of 
      Left err -> error . show $ err
      Right c  -> return . asCNF $ c


-- | Convert parsed CNF to internal representation.
asCNF :: ParseCNF.CNF -> CNF
asCNF (ParseCNF.CNF v c is) =
    CNF { numVars    = v
        , numClauses = c
        , clauses    = Set.fromList . map (map fromIntegral . elems) $ is }

