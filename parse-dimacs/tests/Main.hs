module Main where

import Language.CNF.Parse.ParseDIMACS( parseFile )
import System.Environment( getArgs )

main :: IO ()
main = getArgs >>= parseFile . head >>= print