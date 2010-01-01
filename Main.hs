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
import Data.List( intersperse )
import Data.Version( showVersion )
import Funsat.Solver
    ( solve
    , verify
    , defaultConfig
    , ShowWrapped(..)
    , statTable )
import Funsat.Types( CNF(..), FunsatConfig(..), ConflictCut(..) )
import Paths_funsat( version )
import Prelude hiding ( elem )
import System.Console.GetOpt
import System.Environment( getArgs )
import System.Exit( ExitCode(..), exitWith )
import Data.Time.Clock

import qualified Data.Set as Set
import qualified Language.CNF.Parse.ParseDIMACS as ParseDIMACS
import qualified Text.Tabular as Tabular

import qualified Properties

options :: [OptDescr (Options -> Options)]
options =
    [ Option [] ["restart-at"]
      (ReqArg (\i o ->
          let c = optFunsatConfig o
          in o{ optFunsatConfig = c{configRestart = read i} }) "INT")
      (withDefault (configRestart . optFunsatConfig)
       "Restart after INT conflicts.")

    , Option [] ["restart-bump"]
      (ReqArg (\d o ->
          let c = optFunsatConfig o
          in o{ optFunsatConfig = c{configRestartBump = read d} }) "FLOAT")
      (withDefault (configRestartBump . optFunsatConfig)
       "Alter the number of conflicts required to restart by multiplying by FLOAT.")

    , Option [] ["no-vsids"] (NoArg $ \o ->
          let c = optFunsatConfig o
          in o{ optFunsatConfig = c{configUseVSIDS = False} })
      "Use static variable ordering."

    , Option [] ["no-restarts"] (NoArg $ \o ->
          let c = optFunsatConfig o
          in o{ optFunsatConfig = c{configUseRestarts = False} })
      "Never restart."

    , Option [] ["conflict-cut"]
      (ReqArg (\cut o ->
          let c = optFunsatConfig o
          in o{ optFunsatConfig = c{configCut = readCutOption cut} }) "1|d")
      "Which cut of the conflict graph to use for learning.  1=first UIP; d=decision lit"

    , Option [] ["verify"] (NoArg $ \o -> o{ optVerify = True })
      "Run quickcheck properties and unit tests."

    , Option [] ["profile"] (NoArg $ \o -> o{ optProfile = True })
      "Run solver.  (assumes profiling build)"

    , Option [] ["print-features"] (NoArg $ \o -> o{ optPrintFeatures = True })
      "Print the optimisations the SAT solver supports and exit."

    , Option [] ["version"] (NoArg $ \o -> o{ optVersion = True })
      "Print the version of funsat and exit."
    ]

data Options = Options
    { optVerify        :: Bool
    , optProfile       :: Bool
    , optPrintFeatures :: Bool
    , optFunsatConfig  :: FunsatConfig
    , optVersion       :: Bool }
               deriving (Show)
defaultOptions :: Options
defaultOptions = Options
                 { optVerify        = False
                 , optVersion       = False
                 , optPrintFeatures = False
                 , optFunsatConfig  = defaultConfig }

optUseVsids, optUseRestarts :: Options -> Bool
optUseVsids = configUseVSIDS . optFunsatConfig
optUseRestarts = configUseRestarts . optFunsatConfig

readCutOption ('1':_) = FirstUipCut
readCutOption ('d':_) = DecisionLitCut
readCutOption _       = error "error parsing cut option"

-- | Show default value of option at the end of the given string.
withDefault :: (Show v) => (Options -> v) -> String -> String
withDefault f s = s ++ " Default " ++ show (f defaultOptions) ++ "."

validateArgv :: [String] -> IO (Options, [FilePath])
validateArgv argv = do
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (foldl (flip ($)) defaultOptions o, n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo usageHeader options))

usageHeader :: String
usageHeader = "\nUsage: funsat [OPTION...] cnf-files..."

main :: IO ()
main = do
    (opts, files) <- getArgs >>= validateArgv
    when (optVerify opts) $ do
        Properties.main
        exitWith ExitSuccess

    when (optProfile opts) $ do
        putStrLn "Solving ..."
        Properties.profile
        exitWith ExitSuccess

    when (optVersion opts) $ do
        putStr "funsat "
        putStrLn (showVersion version)
        exitWith ExitSuccess

    putStr "Feature config: "
    putStr . concat $ intersperse ", "
        [ if (optUseVsids opts) then "vsids" else "no vsids"
        , if (optUseRestarts opts) then "restarts" else "no restarts"
        , "unsat checking"
        ]
    putStr "\n"
    when (optPrintFeatures opts) $ exitWith ExitSuccess

    when (null files) $
        ioError (userError (usageInfo usageHeader options))

    forM_ files (parseAndSolve opts)
         where
         parseAndSolve opts path = do
            parseStart <- getCurrentTime
            cnf <- parseCNF path
            putStrLn $ show (numVars cnf) ++ " variables, "
                       ++ show (numClauses cnf) ++ " clauses"
            Set.map seqList (clauses cnf)
              `seq` putStrLn ("Solving " ++ path ++ " ...")
            parseEnd <- getCurrentTime

            startingTime <- getCurrentTime
            let cfg = optFunsatConfig opts
                (solution, stats, rt) = solve cfg cnf
            endingTime <- solution `seq` getCurrentTime
            print solution
            print $ statTable stats `Tabular.combine`
                    Tabular.mkTable
                     [[ WrapString "Parsing time "
                      , WrapString $ show (diffUTCTime parseEnd parseStart) ]
                     ,[ WrapString "Real time "
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

