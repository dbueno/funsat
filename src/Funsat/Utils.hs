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

Utilities.

-}
module Funsat.Utils where

import Control.Monad.ST.Strict
import Control.Monad.State.Lazy hiding ( (>=>), forM_ )
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable hiding ( sequence_ )
import Data.Graph.Inductive.Graph( DynGraph, Graph )
import Data.List( foldl1' )
import Data.Set( Set )
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



-- | The assignment as a list of signed literals.
litAssignment :: IAssignment -> [Lit]
litAssignment mFr = foldr (\i ass -> if mFr!i == 0 then ass
                                     else (L . (mFr!) $ i) : ass)
                          []
                          (range . bounds $ mFr)