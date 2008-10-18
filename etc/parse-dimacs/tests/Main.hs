-- ./dist/build/pdtest/pdtest <cnf-file>
module Main where

import Data.Array.Unboxed
import Language.CNF.Parse.ParseDIMACS
import System.Environment( getArgs )
import Text.Parsec.Error( ParseError )

main :: IO ()
main = getArgs >>= parseFile . head >>= print

class DeepSeq a where
    deepSeq :: a -> b -> b

instance DeepSeq Bool where deepSeq = seq
instance DeepSeq Int where deepSeq = seq
instance DeepSeq a => DeepSeq [a] where
    deepSeq [] x = x
    deepSeq (x:xs) y = deepSeq x $ deepSeq xs y
instance  (DeepSeq a, DeepSeq b) => DeepSeq (Either a b)  where
    deepSeq (Left  a) y = deepSeq a y
    deepSeq (Right b) y = deepSeq b y
instance DeepSeq (UArray a b) where
    deepSeq _ x = x
instance DeepSeq CNF where
    deepSeq c y = deepSeq (numVars c) . deepSeq (numClauses c) . deepSeq (clauses c)
                  $ y
instance DeepSeq ParseError where deepSeq = seq