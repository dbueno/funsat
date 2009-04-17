
{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}

-- | Generates and checks a resolution proof of `Funsat.Types.Unsat' from a
-- resolution trace of a SAT solver (`Funsat.Solver.solve' will generate this
-- trace).  As a side effect of this process an /unsatisfiable core/ is
-- generated from the resolution trace.  This core is a (hopefully small) subset
-- of the input clauses which is still unsatisfiable.  Intuitively, it a concise
-- reason why the problem is unsatisfiable.
--
-- The resolution trace checker is based on the implementation from the paper
-- ''Validating SAT Solvers Using an Independent Resolution-Based Checker:
-- Practical Implementations and Other Applications'' by Lintao Zhang and Sharad
-- Malik.  Unsatisfiable cores are discussed in the paper ''Extracting Small
-- Unsatisfiable Cores from Unsatisfiable Boolean Formula'' by Zhang and Malik.
--
-- 
module Funsat.Resolution
    ( -- * Interface
      genUnsatCore
    , checkDepthFirst
     -- * Data Types
    , ResolutionTrace(..)
    , initResolutionTrace
    , ResolutionError(..)
    , UnsatisfiableCore )
        where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.IntSet( IntSet )
import Data.List( nub )
import Data.Map( Map )
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Funsat.Types
import Funsat.Utils( isSingle, getUnit, isFalseUnder )


-- IDs = Ints
-- Lits = Lits


-- | A resolution trace records how the SAT solver proved the original CNF
-- formula unsatisfiable.
data ResolutionTrace = ResolutionTrace
    { traceFinalClauseId :: ClauseId
      -- ^ The id of the last, conflicting clause in the solving process.

    , traceFinalAssignment :: IAssignment
      -- ^ Final assignment.
      --
      -- /Precondition/: All variables assigned at decision level zero.

    , traceSources :: Map ClauseId [ClauseId]
      -- ^ /Invariant/: Each id has at least one source (otherwise that id
      -- should not even have a mapping).
      --
      -- /Invariant/: Should be ordered topologically backward (?) from each
      -- conflict clause.  (IOW, record each clause id as its encountered when
      -- generating the conflict clause.)

    , traceOriginalClauses :: Map ClauseId Clause
      -- ^ Original clauses of the CNF input formula.

    , traceAntecedents :: Map Var ClauseId }
                       deriving (Show)

initResolutionTrace :: ClauseId -> IAssignment -> ResolutionTrace
initResolutionTrace finalClauseId finalAssignment = ResolutionTrace
    { traceFinalClauseId = finalClauseId
    , traceFinalAssignment = finalAssignment
    , traceSources = Map.empty
    , traceOriginalClauses = Map.empty
    , traceAntecedents = Map.empty }

-- | A type indicating an error in the checking process.  Assuming this
-- checker's code is correct, such an error indicates a bug in the SAT solver.
data ResolutionError =
          ResolveError Var Clause Clause
        -- ^ Indicates that the clauses do not properly resolve on the
        -- variable.

        | CannotResolve [Var] Clause Clause
        -- ^ Indicates that the clauses do not have complementary variables or
        -- have too many.  The complementary variables (if any) are in the
        -- list.

        | AntecedentNotUnit Clause
        -- ^ Indicates that the constructed antecedent clause not unit under
        -- `traceFinalAssignment'.

        | AntecedentImplication (Clause, Lit) Var
        -- ^ Indicates that in the clause-lit pair, the unit literal of clause
        -- is the literal, but it ought to be the variable.

        | AntecedentMissing Var
        -- ^ Indicates that the variable has no antecedent mapping, in which
        -- case it should never have been assigned/encountered in the first
        -- place.
        
        | EmptySource ClauseId
        -- ^ Indicates that the clause id has an entry in `traceSources' but
        -- no resolution sources.

        | OrphanSource ClauseId
        -- ^ Indicates that the clause id is referenced but has no entry in
        -- `traceSources'.
          deriving Show
instance Error ResolutionError where -- Just for the Error monad.

-- checkDepthFirstFix :: (CNF -> (Solution, Maybe ResolutionTrace))
--                    -> Solution
--                    -> ResolutionTrace
--                    -> Either ResolutionError UnsatisfiableCore
-- checkDepthFirstFix solver resTrace =
--     case checkDepthFirst resTrace of
--       Left err -> err
--       Right ucore ->
--           let (sol, rt) solver (rescaleIntoCNF ucore)

-- | Check the given resolution trace of a (putatively) unsatisfiable formula.
-- If the result is `ResolutionError', the proof trace has failed to establish
-- the unsatisfiability of the formula.  Otherwise, an unsatisfiable core of
-- clauses is returned.
--
-- This function simply calls `checkDepthFirst'.
genUnsatCore :: ResolutionTrace -> Either ResolutionError UnsatisfiableCore
genUnsatCore = checkDepthFirst

-- | The depth-first method.
checkDepthFirst :: ResolutionTrace -> Either ResolutionError UnsatisfiableCore
checkDepthFirst resTrace =
    -- Turn internal unsat core into external.
      fmap (map findClause . IntSet.toList)

    -- Check and create unsat core.
    . (`runReader` resTrace)
    . (`evalStateT` ResState { clauseIdMap = traceOriginalClauses resTrace
                             , unsatCore   = IntSet.empty })
    . runErrorT
    $     recursiveBuild (traceFinalClauseId resTrace)
      >>= checkDFClause

  where
      findClause clauseId =
          Map.findWithDefault
          (error $ "checkDFClause: unoriginal clause id: " ++ show clauseId)
          clauseId (traceOriginalClauses resTrace)



-- | Unsatisfiable cores are not unique.
type UnsatisfiableCore = [Clause]


------------------------------------------------------------------------------
-- MAIN INTERNALS
------------------------------------------------------------------------------

data ResState = ResState
    { clauseIdMap :: Map ClauseId Clause
    , unsatCore   :: UnsatCoreIntSet }

type UnsatCoreIntSet = IntSet   -- set of ClauseIds

type ResM = ErrorT ResolutionError (StateT ResState (Reader ResolutionTrace))


-- Recursively resolve the (final, initially) clause with antecedents until
-- the empty clause is created.
checkDFClause :: Clause -> ResM UnsatCoreIntSet
checkDFClause clause =
    if null clause
    then gets unsatCore
    else do l <- chooseLiteral clause
            let v = var l
            anteClause <- recursiveBuild =<< getAntecedentId v
            checkAnteClause v anteClause
            resClause <- resolve (Just v) clause anteClause
            checkDFClause resClause

recursiveBuild :: ClauseId -> ResM Clause
recursiveBuild clauseId = do
    maybeClause <- getClause
    case maybeClause of
      Just clause -> return clause
      Nothing -> do
          sourcesMap <- asks traceSources
          case Map.lookup clauseId sourcesMap of
            Nothing -> throwError (OrphanSource clauseId)
            Just [] -> throwError (EmptySource clauseId)
            Just (firstSourceId:ids) -> recursiveBuildIds clauseId firstSourceId ids
  where
    -- If clause is an *original* clause, stash it as part of the UNSAT core.
    getClause = do
        origMap <- asks traceOriginalClauses
        case Map.lookup clauseId origMap of
          Just origClause -> withClauseInCore $ return (Just origClause)
          Nothing -> Map.lookup clauseId `liftM` gets clauseIdMap

    withClauseInCore =
        (modify (\s -> s{ unsatCore = IntSet.insert clauseId (unsatCore s) }) >>)

recursiveBuildIds :: ClauseId -> ClauseId -> [ClauseId] -> ResM Clause
recursiveBuildIds clauseId firstSourceId sourceIds = do
    rc <- recursiveBuild firstSourceId -- recursive_build(id)
    clause <- foldM buildAndResolve rc sourceIds
    storeClauseId clauseId clause
    return clause

      where
        -- This is the body of the while loop inside the recursiveBuild
        -- procedure in the paper.
        buildAndResolve :: Clause -> ClauseId -> ResM (Clause)
        buildAndResolve clause1 clauseId =
            recursiveBuild clauseId >>= resolve Nothing clause1

        -- Maps ClauseId to built Clause.
        storeClauseId :: ClauseId -> Clause -> ResM ()
        storeClauseId clauseId clause = modify $ \s ->
            s{ clauseIdMap = Map.insert clauseId clause (clauseIdMap s) }


------------------------------------------------------------------------------
-- HELPERS
------------------------------------------------------------------------------


-- | Resolve both clauses on the given variable, and throw a resolution error
-- if anything is amiss.  Specifically, it checks that there is exactly one
-- occurrence of a literal with the given variable (if variable given) in each
-- clause and they are opposite in polarity.
--
-- If no variable specified, finds resolving variable, and ensures there's
-- only one such variable.
resolve :: Maybe Var -> Clause -> Clause -> ResM Clause
resolve maybeV c1 c2 =
    -- Find complementary literals:
    case filter ((`elem` c2) . negate) c1 of
      [l] -> case maybeV of
               Nothing -> resolveVar (var l)
               Just v -> if v == var l
                         then resolveVar v
                         else throwError $ ResolveError v c1 c2
      vs -> throwError $ CannotResolve (nub . map var $ vs) c1 c2
  where
    resolveVar v = return . nub $ deleteVar v c1 ++ deleteVar v c2

    deleteVar v c = c `without` lit v `without` negate (lit v)
    lit (V i) = L i

-- | Get the antecedent (reason) for a variable.  Every variable encountered
-- ought to have a reason.
getAntecedentId :: Var -> ResM ClauseId
getAntecedentId v = do
    anteMap <- asks traceAntecedents
    case Map.lookup v anteMap of
      Nothing   -> throwError (AntecedentMissing v)
      Just ante -> return ante

chooseLiteral :: Clause -> ResM Lit
chooseLiteral (l:_) = return l
chooseLiteral _     = error "chooseLiteral: empty clause"

checkAnteClause :: Var -> Clause -> ResM ()
checkAnteClause v anteClause = do
    a <- asks traceFinalAssignment
    when (not (anteClause `hasUnitUnder` a))
      (throwError $ AntecedentNotUnit anteClause)
    let unitLit = getUnit anteClause a
    when (not $ var unitLit == v)
      (throwError $ AntecedentImplication (anteClause, unitLit) v)
  where
    hasUnitUnder c m = isSingle (filter (not . (`isFalseUnder` m)) c)
