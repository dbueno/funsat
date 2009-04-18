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
import Data.Version( Version(..), showVersion )
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
import qualified Language.CNF.Parse.ParseDIMACS as ParseDIMACS
import qualified Text.Tabular as Tabular

#ifdef TESTING
import qualified Properties
#endif

funsatVersion :: Version
funsatVersion = Version{ versionBranch = [0,6,1]
                       , versionTags   = [] }

options :: [OptDescr (Options -> Options)]
options =
    [ Option [] ["no-vsids"] (NoArg $ \o -> o{ optUseVsids = False })
      "Use static variable ordering."
    , Option [] ["no-restarts"] (NoArg $ \o -> o{ optUseRestarts = False })
      "Never restart."
#ifdef TESTING
    , Option [] ["verify"] (NoArg $ \o -> o{ optVerify = True })
      "Run quickcheck properties and unit tests."
#endif
    , Option [] ["print-features"] (NoArg $ \o -> o{ optPrintFeatures = True })
      "Print the optimisations the SAT solver supports and exit."
    , Option [] ["version"] (NoArg $ \o -> o{ optVersion = True })
      "Print the version of funsat and exit."
    ]

data Options = Options
    { optUseVsids      :: Bool
    , optUseRestarts   :: Bool
    , optVerify        :: Bool
    , optPrintFeatures :: Bool
    , optVersion       :: Bool }
               deriving (Show)
defaultOptions :: Options
defaultOptions = Options
                 { optUseVsids      = True
                 , optUseRestarts   = True
                 , optVerify        = False
                 , optPrintFeatures = False
                 , optVersion       = False }

validateArgv :: [String] -> IO (Options, [FilePath])
validateArgv argv = do
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (foldl (flip ($)) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
    where header = "Usage: funsat [OPTION...] cnf-files..."

main :: IO ()
main = do
    (opts, files) <- getArgs >>= validateArgv
#ifdef TESTING
    when (optVerify opts) $ do
        Properties.main
        exitWith ExitSuccess
#endif

    when (optVersion opts) $ do
        putStrLn (showVersion funsatVersion)
        exitWith ExitSuccess

    putStr $ if (optUseVsids opts) then "vsids" else "no vsids"
    putStr $ if (optUseRestarts opts) then ", restarts" else ", no restarts"
    putStr "\n"
    when (optPrintFeatures opts) $ exitWith ExitSuccess

    forM_ files (parseAndSolve opts)
         where
         parseAndSolve opts path = do
            cnf <- parseCNF path
            putStrLn $ show (numVars cnf) ++ " variables, "
                       ++ show (numClauses cnf) ++ " clauses"
            Set.map seqList (clauses cnf)
              `seq` putStrLn ("Solving " ++ path ++ "...")

            startingTime <- getCurrentTime
            let cfg =
                  (defaultConfig cnf)
                  { configUseVSIDS = optUseVsids opts
                  , configUseRestarts = optUseRestarts opts }
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

seqList l@[] = l
seqList l@(x:xs) = x `seq` seqList xs `seq` l

parseCNF :: FilePath -> IO CNF
parseCNF path = do
    result <- ParseDIMACS.parseFile path
    case result of 
      Left err -> error . show $ err
      Right c  -> return . asCNF $ c


-- | Convert parsed CNF to internal representation.
asCNF :: ParseDIMACS.CNF -> CNF
asCNF (ParseDIMACS.CNF v c is) =
    CNF { numVars    = v
        , numClauses = c
        , clauses    = Set.fromList . map (map fromIntegral . elems) $ is }

