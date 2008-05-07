-- | Grovel over the result file given on the command-line and print a
-- gnuplot-formatted data set to stdout.
module Main where

import Data.Maybe( mapMaybe )
import Text.Regex
import Test.QuickCheck( quickCheck )
import System.Environment( getArgs )

-- | Assume the input contains @n>0@ records delimited at the start by
-- whatever matches regexp.  Each element @s@ of @groups rx f s@ is the output
-- of @f@ when passed (1) a string that starts with a matche for @rx@ and (2)
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
  [filename] <- getArgs
  contents <- readFile filename
  let results = groups satrunRx contents
--   mapM_ (putStrLn . show) (map fst results)
  let times = map findUserTime . map snd $ results
      pairs = zip (map fst results) times
      showPair ([filename], maybeTime) =
          filename ++ " " ++
          case maybeTime of
            Nothing -> maxSecs ++ " # No time information"
            Just time -> time
  mapM_ (putStrLn . showPair) pairs