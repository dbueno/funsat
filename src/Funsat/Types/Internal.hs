{-| Types used internally by funsat. -}
module Funsat.Types.Internal
       ( FunsatState(..)
       , FunMonad
       , FunStats(..)
       , incNumConfl
       , incNumConflTotal
       , incNumImpl
       , incNumDecisions
       , FunsatConfig(..) )
       where

{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}


import Control.Monad.State( modify )
import Data.Int( Int64 )
import Data.Sequence( Seq )
-- import Debug.Trace (trace)
import Funsat.Monad
import Funsat.Types
import Prelude hiding ( sum, concatMap, elem, foldr, foldl, any, maximum )
import qualified Data.Sequence as Seq

data FunsatState s = SC
    { cnf :: CNF                -- ^ The problem.
    , dl :: [Lit]
      -- ^ The decision level (last decided literal on front).

    , watches :: WatchArray s
      -- ^ Invariant: if @l@ maps to @((x, y), c)@, then @x == l || y == l@.

    , learnt :: WatchArray s
      -- ^ Same invariant as `watches', but only contains learned conflict
      -- clauses.

    , propQ :: Seq Lit
      -- ^ A FIFO queue of literals to propagate.  This should not be
      -- manipulated directly; see `Funsat.Solver.enqueue' and `dequeue'.

    , level :: LevelArray s

    , trail :: [Lit]
      -- ^ Chronological trail of assignments, last-assignment-at-head.

    , reason :: ReasonMap
      -- ^ For each variable, the clause that (was unit and) implied its value.

    , varOrder :: VarOrder s

    , resolutionTrace :: PartialResolutionTrace

    , dpllConfig :: FunsatConfig

    , stats :: FunStats } deriving Show

data FunStats =
  FunStats
  { numConfl :: !Int64
    -- ^ The number of conflicts that have occurred since the last restart.

  , numConflTotal :: !Int64
    -- ^ The total number of conflicts.

  , numDecisions :: !Int64
    -- ^ The total number of decisions.

  , numImpl :: !Int64
    -- ^ The total number of implications (propagations).
  } deriving (Eq, Ord, Show)

incNumConfl, incNumConflTotal, incNumImpl, incNumDecisions :: FunMonad s ()
incNumConfl = modify $ \s ->
  let st = stats s in s{ stats = st{numConfl = numConfl st + 1} }
incNumConflTotal = modify $ \s ->
  let st = stats s in s{ stats = st{numConflTotal = numConflTotal st + 1} }
incNumImpl = modify $ \s -> 
  let st = stats s in s{ stats = st{numImpl = numImpl st + 1} }
incNumDecisions = modify $ \s ->
  let st = stats s in s{ stats = st{numDecisions = numDecisions st + 1} }


-- | Our star monad, the DPLL State monad.  We use @ST@ for mutable arrays and
-- references, when necessary.  Most of the state, however, is kept in
-- `FunsatState' and is not mutable.
type FunMonad s = SSTErrMonad (Lit, Clause, ClauseId) (FunsatState s) s

-- | Configuration parameters for the solver.
data FunsatConfig = Cfg
    { configRestart :: !Int64      -- ^ Number of conflicts before a restart.
    , configRestartBump :: !Double -- ^ `configRestart' is altered after each
                                   -- restart by multiplying it by this value.
    , configUseVSIDS :: !Bool      -- ^ If true, use dynamic variable ordering.
    , configUseRestarts :: !Bool }
                  deriving Show

