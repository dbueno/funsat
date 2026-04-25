module Main where

import qualified Integration
import qualified Properties

main :: IO ()
main = do
    Properties.main
    Integration.main
