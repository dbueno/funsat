{-# LANGUAGE DeriveDataTypeable
           , PatternSignatures #-}

{-
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    DPLLSat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with DPLLSat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}


-- | A Haskell implementation of the basic algorithm, including
-- non-chronological backtracking, from ''SAT-MICRO: petit mais costaud!'' by
-- Sylvain Conchon, Johannes Kanig, and Stephane Lescuyer.
--
-- One interesting thing about this implementation is its use of CPS where the
-- OCaml implementation uses exceptions, to handle control flow.
--
-- Optimisations:
-- non-chronological backtracking;
--
-- Backtracking uses the control stack, so, you may want to invoke with
-- something like @
--    sat-micro cnf-file +RTS -K768M -RTS@,
-- depending on the size of the SAT instance.

module SatMicro where

import Control.Monad.Cont hiding (mapM_)
import Control.Monad.State.Strict hiding ((>=>), mapM_)
import Data.Foldable hiding (sequence_)
import Data.List hiding (elem, concat, foldl', foldl, any, all, foldr, maximumBy)
import Data.Map (Map)
import Data.Ord (comparing)
import Data.Set (Set)
import Debug.Trace()
import Prelude hiding (or, and, all, any, elem, minimum, foldr, splitAt
                      , concatMap, foldl, catch, mapM_)
import Text.PrettyPrint.HughesPJ
import qualified Data.Foldable as Foldable
import qualified Data.List as L
import qualified Data.Map as Map
import qualified Data.Set as Set

type CNF = [[Lit]]

data Result = Sat [Lit] | Unsat
instance Show Result where
   show (Sat lits) = "satisfiable: " ++ intercalate " " (map show lits)
   show Unsat      = "unsatisfiable"


newtype Lit = L {unLit :: Int} deriving (Eq, Ord)
inLit :: (Int -> Int) -> Lit -> Lit
{-# INLINE inLit #-}
inLit f = L . f . unLit

instance Show Lit where
    show = show . unLit
instance Read Lit where
    readsPrec i s = map (\(i',s') -> (L i', s')) (readsPrec i s :: [(Int, String)])

instance Num Lit where
    _ + _ = error "+ doesn't make sense for literals"
    _ - _ = error "- doesn't make sense for literals"
    _ * _ = error "* doesn't make sense for literals"
    signum _ = error "signum doesn't make sense for literals"
    negate   = inLit negate
    abs      = inLit abs
    fromInteger l | l == 0    = error "0 is not a literal"
                  | otherwise = L $ fromInteger l


-- | The state of the search process.
data StateContents = S {
      gamma :: Map Lit (Set Lit), -- ^ annotated assignment literals
      delta :: [([Lit], Set Lit)] -- ^ annotated CNF
    }

getGamma :: Lit -> StateContents -> Set Lit
getGamma l e = Map.findWithDefault (error $ show l ++ ": annotation not found")
               l (gamma e)
instance Show StateContents where
    show = render . stateDoc
      where
stateDoc :: StateContents -> Doc
stateDoc (S {gamma=g, delta=d}) =
    brackets (hcat . intersperse space . map (text . show) $ Map.keys g)
    <+> braces (hcat
                . intersperse (comma <> space)
                . map (\(c, a) -> braces (hcat
                                          . intersperse space
                                          . map (text . show) $ c)
                                  <> tups (hcat
                                           . intersperse comma
                                           . map (text . show)
                                           $ Set.toList a))
                $ d)
        where tups p = char '<' <> p <> char '>'


-- | The entry point to the solver.  Searches for a solution to the given
-- satisfiability problem.
dpll :: CNF -> Result
dpll f = (`runCont` id) $ do
    r <- callCC $ \bj -> do
           (Right env) <- bcp bj (initialState f)
           unsat env return
    either (const $ return Unsat) (return . Sat) r

dispatch :: t -> [a] -> [(a, t)]
dispatch d = map (\l -> (l, d))
initialState :: [[Lit]] -> StateContents
initialState f = S {gamma = Map.empty,
                    delta = (dispatch Set.empty f)}

-- bcp either:
--  1. finds a conflict and returns annotation literals (Left)
--  2. computes a new environment (Right)

-- | Given an annotated literal, assume it and propagate this information.
-- This may cause other assignments to take place.
assume :: (Monad m) =>
          (Either (Set Lit) b -> m StateContents)
          -> StateContents
          -> (Lit, Set Lit)
          -> m (Either a StateContents)
{-# INLINE assume #-}
assume bj env (l, s) = -- update only if not present
    if l `Map.member` gamma env
    then return (Right env)
    else bcp bj env{gamma = Map.insert l s (gamma env)}

-- | Boolean constraint propagation.  Under the current assignment, finds any
-- conflicting or unit clauses, and then back jumps or assigns, respectively.
-- If there is no conflict, computes a new environment (@Right@). If this
-- function finds a conflict, calls @bj@ with set of literals annotating the
-- conflicting clause (@Left@).
bcp :: (Monad m) =>
       (Either (Set Lit) b -> m StateContents) -- ^ for backjumping
       -> StateContents
       -> m (Either a StateContents)
bcp bj env = do
    env' <-
        foldM (\env' (cl, a) -> do
                 let (cl_neg, cl') =
                         partition (\l -> negate l `Map.member` gamma env') cl
                 if any (`Map.member` gamma env') cl'
                  then return env'
                  else do
                    -- update clause annotation
                    let a' = foldl'
                             (\set l -> set `Set.union` getGamma (negate l) env')
                             a cl_neg
                    case cl' of
                         []  -> bj (Left a')
                         [f] -> assume bj env' (f, a') >>= return . fromRight
                         _   -> return $ env'{delta = (cl', a'):(delta env')})
        (env{delta = []})
        (delta env)
    return $ Right env'

-- | @unsat@ either:
--
--    1. returns annotation literals (@Left@)
--
--    2. finds satisfying assignment (@Right@)
unsat :: (MonadCont m) =>
         StateContents
         -> (Either (Set Lit) [Lit] -> m (Either (Set Lit) [Lit]))
            -- ^ the back jump function, allowing conflicts to backtrack to
            -- the point where the last involved literal was decided.
         -> m (Either (Set Lit) [Lit])
unsat env bj =
    case delta env of
      [] -> return $ Right $ Map.keys (gamma env)
      ([_],_):_ -> error "unpropagated unit literal"
      ([],_):_  -> error "conflict unresolved"
      _ -> do
        let a = maxSatLit (delta env)
        r <- callCC $ \innerBj -> do
               (Right env') <- assume innerBj env (a, Set.singleton a)
               -- done propagating, no conflicts: continue
               unsat env' return
        case r of
          Left d ->
              if not $ a `elem` d
              then bj (Left d)
              else (callCC $ \innerBj -> do
                      (Right env') <-
                          assume innerBj env (negate a, Set.delete a d)
                      unsat env' bj)
                   >>= either (bj . Left) (return . Right)
          Right _ -> bj r


-- | Returns a literals satisfying a maximal number of clauses.
maxSatLit :: (Foldable t) => t ([Lit], a) -> Lit
maxSatLit cs = (`evalState` Map.empty) $ do
  mapM_ (\(c, _) -> mapM_ incr c) cs
  freqMap <- get
  return $ maximumBy (comparing (valueIn freqMap)) lits
    where
      valueIn :: (Map Lit Int) -> Lit -> Int
      valueIn m l = Map.findWithDefault (error $ "key not found: " ++ show l) l m
      lits = foldl (\cs' (c, _) -> cs' `L.union` c) [] cs

-- * Helpers

fromRight :: Either a b -> b
fromRight (Right a) = a
fromRight (Left _)  = error "fromRight: Left"

incr :: (Num a) => Lit -> State (Map Lit a) ()
{-# INLINE incr #-}
incr l = modify $! Map.insertWith (\_ i -> 1+i) l 1

-- | An example from the paper.
paper1 :: CNF
paper1 =
  [[-1, -3, -4]
  ,[-1, -3, 4]
  ,[2, 3, 5]
  ,[3, 5]
  ,[3, -5]]



-- | Verify a satisfying assignment.
verifyResult :: Result -> CNF -> Bool
verifyResult (Sat m) cnf =
   -- m is well-formed
   all (\l -> not $ negate l `elem` m) m
   && all (\cl -> any (`elem` cl) m) cnf
verifyResult Unsat _ = True
