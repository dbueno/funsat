{-
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}

-- | A simple Parsec module for parsing CNF files in DIMACS format.
module Language.CNF.Parse.ParseDIMACS
    ( parseCNF, CNF(..) ) where

import Text.ParserCombinators.Parsec

data CNF = CNF {numVars :: Int
               ,numClauses :: Int
               ,clauses :: [[Int]]}
           deriving Show

parseCNF :: String              -- ^ The filename.  Used to report errors.
         -> String              -- ^ The contents of the CNF file.
         -> CNF
parseCNF title input =
    case parse cnf title input of
      Left parseError -> error $ "Parse error: " ++ show parseError
      Right cs -> cs

-- A DIMACS CNF file contains a header of the form "p cnf <numVars>
-- <numClauses>" and then a bunch of 0-terminated clauses.
cnf :: Parser CNF
cnf =
   do many comment
      char 'p' ; spaces
      string "cnf" ; spaces
      numVars <- many1 digit ; spaces
      numClauses <- many1 digit
      space `manyTill` newline
      actualClauses <- many1 clause
      return $ CNF (read numVars) (read numClauses) actualClauses

comment :: Parser String
comment = do char 'c' ; manyTill anyChar (try newline)

clause :: Parser [Int]
clause = do many (space <|> newline)
            lits <- between (string "") (char '0') (many1 intSpaces)
            many (space <|> newline)
            return lits

-- Consume all whitespace after the int so the `between' in `clause' matches
-- on "0" at the end.
intSpaces = do i <- int 
               many1 (space <|> newline)
               return i

int :: Parser Int
int = do parity <- option '+' $ choice $ map char "+-"
         first <- posDigit
         rest <- many digit
         return . read $
           case parity of
             '+' -> first : rest
             '-' -> '-' : first : rest
             _  -> error $ "unknown parity syntax: " ++ [parity]

posDigit :: Parser Char
posDigit = oneOf ['1'..'9']

