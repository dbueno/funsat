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

verticalLines numTests s = defaultPlotLines
  { plot_lines_style = s
  , plot_lines_values = map (\p -> [Point (p_x p) 1, p]) $
                        zipWith Point [1..numTests] (repeat 300) }

manyTickAxis = defaultAxis

-- input matrix a list of rows of data; first row has test label
myLayout names matrix = defaultLayout1
    { layout1_plots =
        -- Vertical lines.
        ("", HA_Bottom, VA_Right,
         toPlot (verticalLines (genericLength matrix) (gridLineStyle dimGray))):
        -- Show each column of data, not including the label column.
        concat
        [ [ ("", HA_Bottom, VA_Right, toPlot (plotLines col (lineStyle color)))
          , (name ++ " (" ++ show i ++ ")", HA_Bottom, VA_Left,
             toPlot (plotColumnPoints col (pointStyle color))) ]
        | i     <- [1..length names]
        | name  <- names
        | col   <- pointsRows
        | color <- map toColor colors ] }
  where
    pointStyle color = exes 7 2 color
    gridLineStyle color = dashedLine 0.3 [4.0] (toColor color)
    lineStyle color  = solidLine 0.4 color --dashedLine 0.4 [7.0] color

    black = Color 0 0 0
    red   = Color 1 0 0
    green = Color 0 1 0
    blue  = Color 0 0 1
    dimGray = IntColor 105 105 105
    colors = [blue, red, green]

    -- remove label, convert to doubles, and turn into list of columns
    pointsRows = transpose . map (map read) . map tail $ matrix :: [[Double]]

data IntColor = IntColor Int Int Int
class ToColor a where
    toColor :: a -> Color
instance ToColor Color where
    toColor = id
instance ToColor IntColor where
    toColor (IntColor ri gi bi) = Color (r/255) (g/255) (b/255)
      where r = fromIntegral ri
            g = fromIntegral gi
            b = fromIntegral bi
instance Show Color where
    show (Color r g b) = "Color " ++ intercalate " " [show r, show g, show b]

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
