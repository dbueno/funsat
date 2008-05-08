-- | Grovel over the result file given on the command-line and print a
-- gnuplot-formatted data set to stdout.
module Main where

import Control.Monad
import Data.List( foldl', intercalate, transpose )
import Data.Maybe( mapMaybe )
import Text.Regex
import Test.QuickCheck( quickCheck )
import System.Environment( getArgs )

-- | Assume the input contains @n>0@ records delimited at the start by
-- whatever matches regexp.  Each element @s@ of @groups rx f s@ is the output
-- of @f@ when passed (1) a string that starts with a match for @rx@ and (2)
-- the rest of the string up to (and not including) the next match of @rx@.
--
-- If the regex fails to match at all (i.e. @n=0@), the empty list is
-- returned.
groups :: Regex -> String -> [([String], String)]
groups markerRx s = snd $ groups' markerRx s
  where
    -- Returns the text before the match, if any match, in its first position.
    groups' markerRx s =
        case matchRegexAll markerRx s of
          Nothing -> (s, [])
          Just (beforeMatch, _matched, afterMatch, submatches) ->
              let (beforeNext, retList) = groups' markerRx afterMatch
              in ( beforeMatch, (submatches, beforeNext) : retList )





------------------------------------------------------------------------------
-- Main

satrunRx = mkRegex $
  "Solving ([-_./a-zA-Z0-9]+[.]cnf)"-- ./bench/bf/bf0432-007.cnf

userTimeRx = mkRegex "([[:digit:]]+[.][[:digit:]]+) user"

findUserTime s =
    head `fmap` matchRegex userTimeRx s

maxSecs = "300.0"


main = do
  files@(_:_) <- getArgs
  groupList <- forM files (\file -> readFile file >>= return . groups satrunRx)
               :: IO [[([String], String)]]
  let benchFiles = map (head . fst) $ head groupList
      showTime maybeTime = case maybeTime of
                             Nothing   -> maxSecs
                             Just time -> time
      labelRow = replicate (length files + 1) "LABEL" -- TODO: change me
      dataMatrix =
          (labelRow :)
          . zipWith (:) benchFiles
          . transpose
          . reverse $ 
          foldl' (\matrix grouping ->
                      (map showTime . map findUserTime . map snd $ grouping)
                      : matrix)
                 [] groupList
          :: [[String]]
  forM_ dataMatrix $ putStrLn . intercalate " " 
