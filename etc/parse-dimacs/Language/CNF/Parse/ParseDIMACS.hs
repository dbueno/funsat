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

-- | A simple module for parsing CNF files in DIMACS format.
module Language.CNF.Parse.ParseDIMACS
    ( parseByteString
    , parseFile
    , CNF(..) 
    , Clause )
    where

import Control.Monad
import Data.Array.Unboxed
import Data.ByteString.Lazy( ByteString )
import Prelude hiding (readFile, map)
import Text.Parsec( ParseError, SourceName )
import Text.Parsec.ByteString.Lazy
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim( try, unexpected, runParser )
import qualified Text.Parsec.Token as T


data CNF = CNF
    { numVars    :: !Int
    -- ^ The number of variables in the problem as reported by the cnf header.

    , numClauses :: !Int
    -- ^ The number of clauses in the problem as reported by the cnf header.

    , clauses    :: ![Clause] } deriving Show
type Clause = UArray Int Int

-- | Parse a file containing DIMACS CNF data.
parseFile :: FilePath -> IO (Either ParseError CNF)
parseFile = parseFromFile cnf

-- | Parse a byte string containing DIMACS CNF data.  The source name is only
-- | used in error messages and may be the empty string.
parseByteString :: SourceName -> ByteString -> Either ParseError CNF
parseByteString = runParser cnf ()

-- A DIMACS CNF file contains a header of the form "p cnf <numVars>
-- <numClauses>" and then a bunch of 0-terminated clauses.
cnf :: Parser CNF
cnf = uncurry CNF `fmap` cnfHeader `ap` lexeme (many1 clause)

-- Parses into `(numVars, numClauses)'.
cnfHeader :: Parser (Int, Int)
cnfHeader = do
    whiteSpace
    char 'p' >> many1 space -- Can't use symbol here because it uses
                            -- whiteSpace, which will treat the following
                            -- "cnf" as a comment.
    symbol "cnf"
    (,) `fmap` natural `ap` natural

clause :: Parser (UArray Int Int)
clause = do ints <- lexeme int `manyTill` try (symbol "0")
            return $ listArray (0, length ints - 1) ints


-- token parser
tp = T.makeTokenParser $ T.LanguageDef 
   { T.commentStart = ""
   , T.commentEnd = ""
   , T.commentLine = "c"
   , T.nestedComments = False
   , T.identStart = unexpected "ParseDIMACS bug: shouldn't be parsing identifiers..."
   , T.identLetter = unexpected "ParseDIMACS bug: shouldn't be parsing identifiers..."
   , T.opStart = unexpected "ParseDIMACS bug: shouldn't be parsing operators..."
   , T.opLetter = unexpected "ParseDIMACS bug: shouldn't be parsing operators..."
   , T.reservedNames = ["p", "cnf"]
   , T.reservedOpNames = []
   , T.caseSensitive = True
   }

natural :: Parser Int
natural = fromIntegral `fmap` T.natural tp
int :: Parser Int
int = fromIntegral `fmap` T.integer tp
symbol = T.symbol tp
whiteSpace = T.whiteSpace tp
lexeme = T.lexeme tp