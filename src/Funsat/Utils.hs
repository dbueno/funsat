{-# LANGUAGE MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
            ,FlexibleContexts #-}

{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}


{-|

Generic utilities that happen to be used in the SAT solver.

-}
module Funsat.Utils where

import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ( (>=>), forM_ )
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable hiding ( sequence_ )
import Data.Graph.Inductive.Graph( DynGraph, Graph )
import Data.List( foldl1' )
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace( trace )
import Funsat.Types
import Prelude hiding ( sum, concatMap, elem, foldr, foldl, any, maximum )
import System.IO.Unsafe( unsafePerformIO )
import System.IO( hPutStr, stderr )
import qualified Data.Foldable as Fl
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set



-- | `True' if and only if the object is undefined in the model.
isUndefUnder :: Model a m => a -> m -> Bool
isUndefUnder x m = isUndef $ x `statusUnder` m
    where isUndef (Left ()) = True
          isUndef _         = False

-- | `True' if and only if the object is true in the model.
isTrueUnder :: Model a m => a -> m -> Bool
isTrueUnder x m = isTrue $ x `statusUnder` m
    where isTrue (Right True) = True
          isTrue _            = False

-- | `True' if and only if the object is false in the model.
isFalseUnder :: Model a m => a -> m -> Bool
isFalseUnder x m = isFalse $ x `statusUnder` m
    where isFalse (Right False) = True
          isFalse _             = False

-- * Helpers


-- isUnitUnder c m | trace ("isUnitUnder " ++ show c ++ " " ++ showAssignment m) $ False = undefined

-- | Whether all the elements of the model in the list are false but one, and
-- none is true, under the model.
isUnitUnder :: (Model a m) => [a] -> m -> Bool
{-# SPECIALISE INLINE isUnitUnder :: Clause -> IAssignment -> Bool #-}
isUnitUnder c m = isSingle (filter (not . (`isFalseUnder` m)) c)
                  && not (Fl.any (`isTrueUnder` m) c)

-- Precondition: clause is unit.
-- getUnit :: (Model a m, Show a, Show m) => [a] -> m -> a
-- getUnit c m | trace ("getUnit " ++ show c ++ " " ++ showAssignment m) $ False = undefined

-- | Get the element of the list which is not false under the model.  If no
-- such element, throws an error.
getUnit :: (Model a m, Show a) => [a] -> m -> a
{-# SPECIALISE INLINE getUnit :: Clause -> IAssignment -> Lit #-}
getUnit c m = case filter (not . (`isFalseUnder` m)) c of
                [u] -> u
                xs   -> error $ "getUnit: not unit: " ++ show xs


{-# INLINE mytrace #-}
mytrace :: String -> a -> a
mytrace msg expr = unsafePerformIO $ do
    hPutStr stderr msg
    return expr

outputConflict :: FilePath -> String -> a -> a
outputConflict fn g x = unsafePerformIO $ do writeFile fn g
                                             return x


-- | /O(1)/ Whether a list contains a single element.
isSingle :: [a] -> Bool
{-# INLINE isSingle #-}
isSingle [_] = True
isSingle _   = False

-- | Modify a value inside the state.
modifySlot :: (MonadState s m) => (s -> a) -> (s -> a -> s) -> m ()
{-# INLINE modifySlot #-}
modifySlot slot f = modify $ \s -> f s (slot s)

-- | @modifyArray arr i f@ applies the function @f@ to the index @i@ and the
-- current value of the array at index @i@, then writes the result into @i@ in
-- the array.
modifyArray :: (Monad m, MArray a e m, Ix i) => a i e -> i -> (i -> e -> e) -> m ()
{-# INLINE modifyArray #-}
modifyArray arr i f = readArray arr i >>= writeArray arr i . (f i)

-- | Same as @newArray@, but helping along the type checker.
newSTUArray :: (MArray (STUArray s) e (ST s), Ix i)
               => (i, i) -> e -> ST s (STUArray s i e)
newSTUArray = newArray

newSTArray :: (MArray (STArray s) e (ST s), Ix i)
              => (i, i) -> e -> ST s (STArray s i e)
newSTArray = newArray


-- | Count the number of elements in the list that satisfy the predicate.
count :: (a -> Bool) -> [a] -> Int
count p = foldl' f 0
    where f x y | p y       = x + 1
                | otherwise = x

-- | /O(1)/ @argmin f x y@ is the argument whose image is least under @f@; if
-- the images are equal, returns the first.
argmin :: Ord b => (a -> b) -> a -> a -> a
argmin f x y = if f x <= f y then x else y

-- | /O(length xs)/ @argminimum f xs@ returns the value in @xs@ whose image
-- is least under @f@; if @xs@ is empty, throws an error.
argminimum :: Ord b => (a -> b) -> [a] -> a
argminimum f = foldl1' (argmin f)


-- | Show the value with trace, then return it.  Useful because you can wrap
-- it around any subexpression to print it when it is forced.
tracing :: (Show a) => a -> a
tracing x = trace (show x) x

-- | Returns a predicate which holds exactly when both of the given predicates
-- hold.
(.&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
p .&&. q = \x -> p x && q x


-- | Generate a cut using the given UIP node.  The cut generated contains
-- exactly the (transitively) implied nodes starting with (but not including)
-- the UIP on the conflict side, with the rest of the nodes on the reason
-- side.
uipCut :: (Graph gr) =>
          [Lit]                 -- ^ decision literals
       -> FrozenLevelArray
       -> gr a b                -- ^ conflict graph
       -> Graph.Node            -- ^ unassigned, implied conflicting node
       -> Graph.Node            -- ^ a UIP in the conflict graph
       -> Cut Set gr a b
uipCut dlits levelArr conflGraph conflNode uip =
    Cut { reasonSide   = Set.filter (\i -> levelArr!(V $ abs i) > 0) $
                         allNodes Set.\\ impliedByUIP
        , conflictSide = impliedByUIP
        , cutUIP       = uip
        , cutGraph     = conflGraph }
    where
      -- Transitively implied, and not including the UIP.  
      impliedByUIP = Set.insert extraNode $
                     Set.fromList $ tail $ DFS.reachable uip conflGraph
      -- The UIP may not imply the assigned conflict variable which needs to
      -- be on the conflict side, unless it's a decision variable or the UIP
      -- itself.
      extraNode = if L (negate conflNode) `elem` dlits || negate conflNode == uip
                  then conflNode -- idempotent addition
                  else negate conflNode
      allNodes = Set.fromList $ Graph.nodes conflGraph


-- | Generate a learned clause from a cut of the graph.  Returns a pair of the
-- learned clause and the decision level to which to backtrack.
cutLearn :: (Graph gr, Foldable f) => IAssignment -> FrozenLevelArray
         -> Cut f gr a b -> (Clause, Int)
cutLearn a levelArr cut =
    ( clause
      -- The new decision level is the max level of all variables in the
      -- clause, excluding the uip (which is always at the current decision
      -- level).
    , maximum0 (map (levelArr!) . (`without` V (abs $ cutUIP cut)) . map var $ clause) )
  where
    -- The clause is composed of the variables on the reason side which have
    -- at least one successor on the conflict side.  The value of the variable
    -- is the negation of its value under the current assignment.
    clause =
        foldl' (\ls i ->
                    if any (`elem` conflictSide cut) (Graph.suc (cutGraph cut) i)
                    then L (negate $ a!(V $ abs i)):ls
                    else ls)
               [] (reasonSide cut)
    maximum0 [] = 0            -- maximum0 has 0 as its max for the empty list
    maximum0 xs = maximum xs


-- | Creates the conflict graph, where each node is labeled by its literal and
-- level.
--
-- Useful for getting pretty graphviz output of a conflict.
mkConflGraph :: DynGraph gr =>
                IAssignment
             -> FrozenLevelArray
             -> Map Var Clause
             -> [Lit]           -- ^ decision lits, in rev. chron. order
             -> (Lit, Clause)   -- ^ conflict info
             -> gr CGNodeAnnot ()
mkConflGraph mFr lev reasonMap _dlits (cLit, confl) =
    Graph.mkGraph nodes' edges'
  where
    -- we pick out all the variables from the conflict graph, specially adding
    -- both literals of the conflict variable, so that that variable has two
    -- nodes in the graph.
    nodes' =
            ((0, CGNA (L 0) (-1)) :) $ -- lambda node
            ((unLit cLit, CGNA cLit (-1)) :) $
            ((negate (unLit cLit), CGNA (negate cLit) (lev!(var cLit))) :) $
            -- annotate each node with its literal and level
            map (\v -> (unVar v, CGNA (varToLit v) (lev!v))) $
            filter (\v -> v /= var cLit) $
            toList nodeSet'
          
    -- node set includes all variables reachable from conflict.  This node set
    -- construction needs a `seen' set because it might infinite loop
    -- otherwise.
    (nodeSet', edges') =
        mkGr Set.empty (Set.empty, [ (unLit cLit, 0, ())
                                   , ((negate . unLit) cLit, 0, ()) ])
                       [negate cLit, cLit]
    varToLit v = (if v `isTrueUnder` mFr then id else negate) $ L (unVar v)

    -- seed with both conflicting literals
    mkGr _ ne [] = ne
    mkGr (seen :: Set Graph.Node) ne@(nodes, edges) (lit:lits) =
        if haveSeen
        then mkGr seen ne lits
        else newNodes `seq` newEdges `seq`
             mkGr seen' (newNodes, newEdges) (lits ++ pred)
      where
        haveSeen = seen `contains` litNode lit
        newNodes = var lit `Set.insert` nodes
        newEdges = [ ( litNode (negate x) -- unimplied lits from reasons are
                                          -- complemented
                     , litNode lit, () )
                     | x <- pred ] ++ edges
        pred = filterReason $
               if lit == cLit then confl else
               Map.findWithDefault [] (var lit) reasonMap `without` lit
        filterReason = filter ( ((var lit /=) . var) .&&.
                                ((<= litLevel lit) . litLevel) )
        seen' = seen `with` litNode lit
        litLevel l = if l == cLit then length _dlits else lev!(var l)
        litNode l =              -- lit to node
            if var l == var cLit -- preserve sign of conflicting lit
            then unLit l
            else (abs . unLit) l


