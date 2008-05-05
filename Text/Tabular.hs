
{-|

Tabular output.

Converting any matrix of showable data types into a tabular form for which the
layout is automatically done properly.  Currently there is no maximum row
width, just a dynamically-calculated column width.

If the input matrix is mal-formed, the largest well-formed submatrix is
chosen.  That is, elements along too-long dimensions are chopped off.

-}
module Text.Tabular( T(..), mkTable, combine, unTable ) where

import Data.List( intercalate )

newtype T a = T [Row a]            -- table is a list of rows
newtype Row a = Row [Cell a]
data Cell a = Cell { cellWidth :: Int
                   -- the width of a cell is the max of the widths of the
                   -- string representations of all the elements in the column
                   -- in which this cell occurs
                   , cellData :: a } -- element printed in box of colWidth

mkTable :: (Show a) => [[a]] -> T a
mkTable rows = T $ mkRows rows
  where
    widths      = colWidths rows
    mkRows rows = [ Row (map mkCell (zip widths row)) | row <- rows ]
    mkCell      = uncurry Cell

unTable :: T a -> [[a]]
unTable (T rows) = [ map cellData r | (Row r) <- rows ]

combine :: (Show a) => T a -> T a -> T a
-- slow impl but works
combine t t' = mkTable (unTable t ++ unTable t')

-- returns a list of the widths of each column
colWidths :: (Show a) => [[a]] -> [Int]
colWidths = map (maximum . map (length . show)) . zipn

-- Pretty, columnar output.
instance (Show a) => Show (T a) where
    show (T rows) = intercalate "\n" $ map showRow rows 
        where
          showRow (Row cols) = intercalate " " $ colStrings
            where
              colStrings = [ padString (cellWidth c) (show d)
                             | c@(Cell {cellData=d}) <- cols ]

padString maxWidth str = str ++ replicate padLen ' '
    where padLen = maxWidth - length str

zipn xss | any null xss = []
zipn xss = map head xss : zipn (map tail xss)

                  