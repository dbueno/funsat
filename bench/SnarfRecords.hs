{-# OPTIONS_GHC -fglasgow-exts #-}

-- | Grovel over the result file given on the command-line and print a
-- gnuplot-formatted data set to stdout.
--
-- Example usage:
--
-- runghc SnarfRecords.hs result.1 result.2 > result1-2.dat
module Main where

import Control.Monad
import Data.List( foldl', intercalate, transpose, genericLength )
import Data.Maybe( mapMaybe )
import Debug.Trace( trace )
import Graphics.Rendering.Chart
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

plotColumnPoints col s = defaultPlotPoints
  { plot_points_style = s
  , plot_points_values = zipWith Point [1..] col }

plotLines col s = defaultPlotLines
  { plot_lines_style = s
  , plot_lines_values = [zipWith Point [1..] col] }

manyTickAxis = defaultAxis

myLayout names matrix = defaultLayout1
    { layout1_plots =
        -- Show each column of data, not including the label column.
        concat
        [ [ ("", HA_Bottom, VA_Right, toPlot (plotLines col (lineStyle color)))
          , (name ++ " (" ++ show i ++ ")", HA_Bottom, VA_Left,
             toPlot (plotColumnPoints col (pointStyle color))) ]
        | i     <- [1..length names]
        | name  <- names
        | col   <- pointsRows
        | color <- colors ] }
  where
    pointStyle color = exes 7 2 color
    lineStyle color  = solidLine 1 color

    black = Color 0 0 0
    red   = Color 1 0 0
    green = Color 0 1 0
    blue  = Color 0 0 1
    colors = [black, red, green, blue]

    -- remove label and convert to doubles
    pointsRows = transpose . map (map read) . map tail $ matrix :: [[Double]]

savePNG names matrix =
    renderableToPNGFile (toRenderable (myLayout names matrix)) 1024 768 "test.png"


------------------------------------------------------------------------------
-- Main

satrunRx = mkRegex $
  "Solving ([-_./a-zA-Z0-9]+[.]cnf)"-- ./bench/bf/bf0432-007.cnf

userTimeRx = mkRegex "([[:digit:]]+[.][[:digit:]]+) user"

findUserTime s =
    head `fmap` matchRegex userTimeRx s

maxSecs = "300.0"

tracing x = trace (show x) $ x

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
  putStrLn "Saving PNG..." >> savePNG (tail labelRow) (tail dataMatrix)
--   forM_ dataMatrix $ putStrLn . intercalate " " 
