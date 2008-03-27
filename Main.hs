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

import DPLLSat( solve1
              , CNF
              , GenCNF(..)
              , Solution(..)
              , verify )
import System.Environment ( getArgs )
import Control.Monad ( when )
import qualified Data.Set as Set
import qualified Language.CNF.Parse.ParseDIMACS as ParseCNF


#ifdef TESTING
import qualified Properties
#endif

main :: IO ()
main =
    getArgs >>= \args ->
    case args of
      [] -> putStrLn usage
#ifdef TESTING
      "-verify":_         -> Properties.main
#endif
      "-print-features":_ -> putStrLn features
      path:_ -> readFile path >>= parseAndSolve
         where
           parseAndSolve contents = do
              let cnf = asCNF $ ParseCNF.parseCNF path contents
              putStrLn $ show (numVars cnf) ++ " variables, "
                         ++ show (numClauses cnf) ++ " clauses"
              Set.map seqList (clauses cnf)
                `seq` putStrLn ("Solving " ++ path ++ "...")
              let solution = solve1 cnf
              putStrLn $ show solution
              case solution of
                Sat m -> when (not $ verify m cnf) $
                           do putStrLn "VERIFICATION ERROR!"
#ifdef TESTING
                              putStrLn $
                                "Minimal erroneous CNF:\n"
                                ++ show (Properties.minimalError cnf)
#endif TESTING
                Unsat -> return ()


usage = "Usage:\ndsat <cnf-filename>"

features = "watched literals, conflict clause learning, non-chronological backtracking, restarts"

seqList l@[] = l
seqList l@(x:xs) = x `seq` seqList xs `seq` l


-- | Convert parsed CNF to internal representation.
asCNF :: ParseCNF.CNF -> CNF
asCNF (ParseCNF.CNF v c is) =
    CNF {numVars = v
        ,numClauses = c
        ,clauses = Set.fromList . map (map fromIntegral) $ is}

