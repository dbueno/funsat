{-# LANGUAGE EmptyDataDecls #-}


{-
    This file is part of funsat.

    funsat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    funsat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with funsat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}

-- | Generates resolution proof of UNSAT from a trace of Funsat.  This is
-- based on the implementation discussed in the paper ''Validating SAT Solvers
-- Using an Independent Resolution-Based Checker: Practical Implementations
-- and Other Applications'' by Lintao Zhang and Sharad Malik.
--
-- This module also facilitates /unsatisfiable core/ generation from the
-- resolution trace, as discussed in the paper ''Extracting Small
-- Unsatisfiable Cores from Unsatisfiable Boolean Formula'' by Zhang and
-- Malik.
module Funsat.Resolution
    ( -- * Interface
      checkDepthFirst
     -- * Data Types
    , ResolutionTrace(..)
    , ResolutionError(..)
    , UnsatisfiableCore
    , ClauseId )
        where

import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.Map( Map )
import Data.Maybe( fromJust )
import qualified Data.Map as Map
import Funsat.Types


-- IDs = Ints
-- Lits = Lits

data ResolutionTrace = ResolutionTrace
    { traceFinalClauseId :: ClauseId
    , traceFinalAssignment :: IAssignment
    , traceSources :: Map ClauseId [ClauseId]
      -- ^ Invariant: Each id has at least one source (otherwise that id
      -- should not even have a mapping).
    , traceAntecedents :: Map Var ClauseId }

type ClauseId = Int

-- | An error indicating some sort of bug either in the SAT solver, its
-- trace-generating code, or this code, or any combination of the three.
data ResolutionError =
          ResolveError Var Clause Clause
          -- ^ Returned if the clauses do not properly resolve on the
          -- variable.

        | AntecedentError Var Clause
        -- ^ Returned if the clause ought to be but is not a proper antecedent
        -- of the variable.
        
        | EmptySource ClauseId
        -- ^ Returned if the clause id has an entry in `traceSources' but no
        -- resolution sources.

        | OrphanSource ClauseId
        -- ^ Returned if the clause id is referenced but has no entry in
        -- `traceSources'.
          deriving Show

data ResState = ResState
    { resTrace :: ResolutionTrace
    , clauseIdMap :: Map ClauseId Clause }

type ResM = ErrorT ResolutionError (StateT ResState (Reader ResolutionTrace))

-- | Unsatisfiable cores are not unique.
type UnsatisfiableCore = [Clause]



-- | The depth-first method.
checkDepthFirst :: ResolutionTrace -> Either ResolutionError UnsatisfiableCore
checkDepthFirst resTrace =
    let clauseId = traceFinalClauseId resTrace
    in -- TODO here turn clauseIdMap into a list of clauses
      (`runReader` undefined) . (`evalStateT` undefined) . runErrorT $ do
          cl <- recursiveBuild clauseId
          checkDFClause cl

checkDFClause :: Clause -> ResM UnsatisfiableCore
checkDFClause clause =
    if null clause
    then return [] -- TODO return either a real core or something that can be
                   -- turned into one.

         -- TODO check whether anteClause is unit under the trace assignment
         -- and the unit literal corresponds to v.  If not, throw error.
    else do l <- chooseLiteral clause
            let v = var l
            anteClause <- recursiveBuild =<< (getAntecedentId v)
            resClause <- resolve (Just v) clause anteClause
            checkDFClause resClause

-- | Resolve both clauses on the given variable, and throw a resolution error
-- if anything is amiss.  Specifically, it checks that there is exactly one
-- occurrence of a literal with the given variable in each clause and they are
-- opposite in polarity.
--
-- If no variable specified, find resolving variable.
resolve :: Maybe Var -> Clause -> Clause -> ResM Clause
resolve maybeV c1 c2 =
    if not vproper
    then throwError (ResolveError v c1 c2)
    else return $ deleteVar v c1 ++ deleteVar v c2
      where
        deleteVar = undefined
        vproper = undefined
        v = undefined

getAntecedentId :: Var -> ResM ClauseId
getAntecedentId v = do
    anteMap <- asks traceAntecedents
    return $ Map.findWithDefault (error $ "getAntecedentId: no ante: " ++ show v)
             v anteMap

chooseLiteral :: Clause -> ResM Lit
chooseLiteral (l:_) = return l

-- Depth-first approach from the ''Validating SAT Solvers'' paper.
recursiveBuild :: ClauseId -> ResM Clause
recursiveBuild clauseId {-id-} = do
    cMap <- gets clauseIdMap
    sourcesMap <- asks traceSources
    case Map.lookup clauseId cMap of
      Just clause -> return clause
      Nothing -> do
          case Map.lookup clauseId sourcesMap of
            Nothing -> throwError (OrphanSource clauseId)
            Just [] -> throwError (EmptySource clauseId)
            Just (firstSourceId:ids) -> recursiveBuildIds clauseId firstSourceId ids

recursiveBuildIds clauseId firstSourceId sourceIds = do
          rc <- recursiveBuild firstSourceId -- recursive_build(id)
          clause <- foldM buildAndResolve rc sourceIds
          storeClauseId clauseId clause
          return clause

            where
              -- This is the while loop inside the recursiveBuild procedure in the
              -- paper.
              buildAndResolve :: Clause -> ClauseId -> ResM (Clause)
              buildAndResolve clause1 clauseId = do
                  clause2 <- recursiveBuild clauseId
                  resolve Nothing clause1 clause2

              -- Maps ClauseId to built Clause.
              storeClauseId :: ClauseId -> Clause -> ResM ()
              storeClauseId clauseId clause =
                  modify $ \s ->
                      s{ clauseIdMap = Map.insert clauseId clause (clauseIdMap s) }


instance Error ResolutionError where