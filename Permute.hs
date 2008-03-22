#!env runghc

-- Permute the lines given on stdin.

import System.Random

main = do
  s <- getContents
  permute (lines s) >>= putStr . unlines

permute :: [a] -> IO [a]
permute [] = return []
permute xs = do
  idx <- getStdRandom (randomR (0, length xs - 1))
  case splitAt idx xs of
    (pfx, x:xs') -> do perm <- permute $ pfx ++ xs'
                       return $ x : perm
    _            -> error "permute: bug"
