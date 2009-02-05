

-- | A circuit is a standard one of among many ways of representing a
-- propositional logic formula.  This module provides a flexible circuit type
-- class and various representations that admit efficient conversion to funsat
-- CNF.
--
-- The implementation for this module was adapted from
-- <http://okmij.org/ftp/Haskell/DSLSharing.hs>.
module Funsat.Circuit
    (
    -- ** Circuit type class
      Circuit(..)
    , GeneralCircuit(..)

    -- ** Explicit sharing circuit
    , ShareC(..)
    , FrozenShareC(..)
    , CircuitHash
    , CCode(..)
    , HLC(..)
    , CMaps(..)
    , emptyCMaps

    -- ** Explicit tree circuit
    , TreeC(..)

    -- *** Circuit simplification
    , simplifyCircuit

    -- ** Circuit evaluator
    , BEnv(..)
    , EvalC(..)
    , evalCircuit

    -- ** Convert circuit to CNF
    , toCNF
    )
where

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


import Control.Monad.Error hiding ((>=>), forM_)
import Control.Monad.Reader
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Control.Monad.Writer.Class
import Data.Graph.Inductive.Graph( DynGraph, Graph, LNode )
import Data.Graph.Inductive.Tree()
import Data.GraphViz( DotGraph, graphToDot )
import Data.IntMap( IntMap )
import Data.List( nub )
import Data.Map( Map )
import Data.Maybe()
import Data.Monoid
import Data.Ord()
import Data.Sequence( Seq )
import Funsat.Types ( CNF(..), Lit(..), Var(..), var )
import Prelude hiding( not, and, or )

import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.GraphViz as GraphViz
import qualified Data.GraphViz.Attributes as Attribute
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Prelude as Prelude



-- * Circuit representation


-- | A class representing a grammar for logical circuits.  Currently only `ite',
-- `onlyif', and `iff' have default implementations.  Instances must implement
-- `true', `false', `input', `and', `or', and `not'.
--
-- /TODO/ Implement defaults so that all instances only /need/ implement an
-- adequate (complete) boolean base, not all operations.
class Circuit repr where
    true  :: (Ord var, Show var) => repr var
    false :: (Ord var, Show var) => repr var
    input :: (Ord var, Show var) => var -> repr var
    and   :: (Ord var, Show var) => repr var -> repr var -> repr var
    or    :: (Ord var, Show var) => repr var -> repr var -> repr var
    not   :: (Ord var, Show var) => repr var -> repr var

    -- | If-then-else circuit.  @ite c t e@ returns a circuit that evaluates to
    -- @t@ when @c@ evaluates to true, and @e@ otherwise.
    ite :: (Ord var, Show var) => repr var -> repr var -> repr var -> repr var
    ite c t f = (c `and` t) `or` (not c `and` f)

    -- | @`onlyif' p q@ is equivalent to @not p `or` q@.
    onlyif :: (Ord var, Show var) => repr var -> repr var -> repr var
    onlyif p q = not p `or` q

    -- | @`iff' p q@ is equivalent to @(p `onlyif` q) `and` (q `onlyif` p)@.
    iff :: (Ord var, Show var) => repr var -> repr var -> repr var
    iff p q = (p `onlyif` q) `and` (q `onlyif` p)

    -- | @`xor' p q@ is equivalent to @(p `or` q) `and` not (p `and` q)@.
    xor :: (Ord var, Show var) => repr var -> repr var -> repr var
    xor p q = (p `or` q) `and` not (p `and` q)

-- | Instances of `GeneralCircuit' admit converting on circuit representation to
-- another.
class GeneralCircuit c where
    generalCircuit :: (Circuit cOut, Ord var, Show var) => c var -> cOut var



-- ** Explicit sharing circuit

-- The following business is for elimination of common subexpressions from
-- boolean functions.  Part of conversion to CNF.

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShareC'.
newtype ShareC v = ShareC { unShareC :: State (CMaps v) CCode }

-- | A shared circuit that has already been constructed.
newtype FrozenShareC v = FrozenShareC (CCode, CMaps v)

-- | Reify a sharing circuit.
runShareC :: ShareC v -> FrozenShareC v
runShareC = FrozenShareC . (`runState` emptyCMaps 1) . unShareC

instance GeneralCircuit ShareC where
    generalCircuit = generalCircuit . runShareC

instance GeneralCircuit FrozenShareC where
    generalCircuit (FrozenShareC (code, maps)) = go code
      where
        go (CTrue{})    = true
        go (CFalse{})   = false
        go (CVar _ i)   = input $ getChildren i varMap
        go (CAnd _ i)   = let (lcode, rcode) = getChildren i andMap
                          in and (go lcode) (go rcode)
        go (COr _ i)    = let (lcode, rcode) = getChildren i orMap
                          in or (go lcode) (go rcode)
        go (CNot _ i)   = let ncode = getChildren i notMap
                          in not (go ncode)

        getChildren int codeMap =
            IntMap.findWithDefault (error $ "fromCCode: unknown code: " ++ show int)
            int (codeMap maps)

type CircuitHash = Int

-- | A `CCode' is a flattened tree node which has been assigned a unique number
-- in the corresponding map inside `CMaps', which indicates children, if any.
--
-- For example, @CAnd Nothing i@ has the two children of the tuple @lookup i
-- (andMap cmaps)@ assuming @cmaps :: CMaps v@.
data CCode = CTrue  { hlc         :: Maybe HLC
                    , circuitHash :: !CircuitHash }
           | CFalse { hlc         :: Maybe HLC
                    , circuitHash :: !CircuitHash }
           | CAnd   { hlc         :: Maybe HLC
                    , circuitHash :: !CircuitHash }
           | COr    { hlc         :: Maybe HLC
                    , circuitHash :: !CircuitHash }
           | CNot   { hlc         :: Maybe HLC
                    , circuitHash :: !CircuitHash }
           | CVar   { hlc         :: Maybe HLC
                    , circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show)

-- | High-level circuit.
data HLC = Xor CCode CCode
         | Onlyif CCode CCode
         | Iff CCode CCode
           deriving (Eq, Ord, Show)

-- | Maps used to implement the common-subexpression sharing implementation of
-- the `Circuit' class.  See `ShareC'.
--
-- /TODO/: implement using bimaps if this part is slow.
data CMaps v = CMaps
    { hashCount :: CircuitHash
    -- ^ Source of unique IDs used in `ShareC' circuit generation.  This
    -- numbering is guaranteed to start at 1 and continue upward by ones when
    -- using `runShareC' to freeze the circuit.

    , trueInt   :: Maybe CCode
    , falseInt  :: Maybe CCode
    , varMap    :: IntMap v
     -- ^ Mapping of generated integer IDs to variables.

    , andMap    :: IntMap (CCode, CCode)
    , orMap     :: IntMap (CCode, CCode)
    , notMap    :: IntMap CCode }
               deriving (Eq, Ord, Show)

-- | A `CMaps' from an initial `hashCount'.
emptyCMaps :: CircuitHash -> CMaps v
emptyCMaps i = CMaps
    { hashCount = i
    , trueInt   = Nothing
    , falseInt  = Nothing
    , varMap    = IntMap.empty
    , andMap    = IntMap.empty
    , orMap     = IntMap.empty
    , notMap    = IntMap.empty }

-- | Find key mapping to given value.
lookupv :: Eq v => v -> IntMap v -> Maybe Int
lookupv v = IntMap.foldWithKey 
              (\k e z -> maybe (if e == v then Just k else Nothing) (const z) z) 
              Nothing

-- prj: "projects relevant map out of state"
-- upd: "stores new map back in state"
recordC :: (Eq a) =>
           (CircuitHash -> b)
        -> (CMaps v -> IntMap a)            -- ^ prj
        -> (CMaps v -> IntMap a -> CMaps v) -- ^ upd
        -> a
        -> State (CMaps v) b
recordC _ _ _ x | x `seq` False = undefined
recordC cons prj upd x = do
  s <- get
  maybe (do let s' = upd (s{ hashCount = succ (hashCount s) })
                         (IntMap.insert (hashCount s) x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons $ hashCount s))
        (return . cons) $ lookupv x (prj s)

instance Circuit ShareC where
    true = ShareC $ do
               ti <- gets trueInt
               case ti of
                 Nothing -> do
                     i <- gets hashCount
                     let c = CTrue Nothing i
                     modify $ \s -> s{ hashCount = succ i, trueInt = Just c }
                     return c
                 Just c -> return c
    false = ShareC $ do
               ti <- gets falseInt
               case ti of
                 Nothing -> do
                     i <- gets hashCount
                     let c = CFalse Nothing i
                     modify $ \s -> s{ hashCount = succ i, falseInt = Just c }
                     return c
                 Just c -> return c
    input v = ShareC $ recordC (CVar Nothing) varMap (\s e -> s{ varMap = e }) v
    and e1 e2 = ShareC $ do
                    h1 <- unShareC e1
                    h2 <- unShareC e2
                    recordC (CAnd Nothing) andMap (\s e -> s{ andMap = e}) (h1, h2)
    or  e1 e2 = ShareC $ do
                    h1 <- unShareC e1
                    h2 <- unShareC e2
                    recordC (COr Nothing) orMap (\s e -> s{ orMap = e }) (h1, h2)
    not e = ShareC $ do
                h <- unShareC e
                recordC (CNot Nothing) notMap (\s e' -> s{ notMap = e' }) h
    xor l r = ShareC $ do
                  hl <- unShareC l ; hr <- unShareC r
                  let from = Xor hl hr
                  liftM (\c -> c{ hlc = Just from }) . unShareC $
                        (l `or` r) `and` not (l `and` r)
    iff l r = ShareC $ do
                  hl <- unShareC l ; hr <- unShareC r
                  let from = Iff hl hr
                  liftM (\c -> c{ hlc = Just from }) . unShareC $
                        (l `onlyif` r) `and` (r `onlyif` l)
    onlyif l r = ShareC $ do
                     hl <- unShareC l ; hr <- unShareC r
                     let from = Onlyif hl hr
                     liftM (\c -> c{ hlc = Just from }) . unShareC $
                           not l `or` r
              

-- ** Explicit tree circuit

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.
data TreeC v = TTrue
             | TFalse
             | TLeaf v
             | TAnd (TreeC v) (TreeC v)
             | TOr (TreeC v) (TreeC v)
             | TXor (TreeC v) (TreeC v)
             | TNot (TreeC v)
               deriving (Show)

instance Circuit TreeC where
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot
    xor   = TXor

instance GeneralCircuit TreeC where
    generalCircuit TTrue        = true
    generalCircuit TFalse       = false
    generalCircuit (TLeaf l)    = input l
    generalCircuit (TAnd t1 t2) = and (generalCircuit t1) (generalCircuit t2)
    generalCircuit (TOr t1 t2)  = or (generalCircuit t1) (generalCircuit t2)
    generalCircuit (TXor t1 t2) = xor (generalCircuit t1) (generalCircuit t2)
    generalCircuit (TNot t)     = not (generalCircuit t)

-- ** Circuit evaluator

type BEnv v = Map v Bool

-- | A circuit evaluator, that is, a circuit represented as a function from
-- variable values to booleans.
newtype EvalC v = EvalC { unEvalC :: BEnv v -> Bool }

-- | Evaluate a circuit given inputs.
evalCircuit :: BEnv v -> EvalC v -> Bool
evalCircuit = flip unEvalC

instance Circuit EvalC where
    true    = EvalC $ const True
    false   = EvalC $ const False
    input v = EvalC $ \env ->
                      Map.findWithDefault
                        (error $ "EvalC: no such var: " ++ show v
                                 ++ " in " ++ show env)
                         v env
    and c1 c2 = EvalC (\env -> unEvalC c1 env && unEvalC c2 env)
    or  c1 c2 = EvalC (\env -> unEvalC c1 env || unEvalC c2 env)
    not c     = EvalC (\env -> Prelude.not $ unEvalC c env)

-- ** Graph circuit
{-

newtype GraphC v = GraphC
    { unGraphC :: State Graph.Node (Graph.Node,
                                    [Graph.LNode String],
                                    [Graph.LEdge ()]) }

runGraphC :: (DynGraph gr) => GraphC v -> gr String ()
runGraphC graphBuilder =
    let (_, nodes, edges) = evalState (unGraphC graphBuilder) 1
    in Graph.mkGraph nodes edges

instance Circuit GraphC where
    input v = GraphC $ do
        n <- newNode
        return $ (n, [(n, show v)], [])

    true = GraphC $ do
        n <- newNode
        return $ (n, [(n, "true")], [])

    false = GraphC $ do
        n <- newNode
        return $ (n, [(n, "false")], [])

    and gs1 gs2 = GraphC $ do
        (lNode, lNodes, lEdges) <- unGraphC gs1
        (rNode, rNodes, rEdges) <- unGraphC gs2
        n <- newNode
        return (n, (n, "AND") : lNodes ++ rNodes,
                   (lNode, n, ()) : (rNode, n, ()) : lEdges ++ rEdges)

    or gs1 gs2 = GraphC $ do
        (lNode, lNodes, lEdges) <- unGraphC gs1
        (rNode, rNodes, rEdges) <- unGraphC gs2
        n <- newNode
        return (n, (n, "OR") : lNodes ++ rNodes,
                   (lNode, n, ()) : (rNode, n, ()) : lEdges ++ rEdges)

    not gs = GraphC $ do
        (node, nodes, edges) <- unGraphC gs
        n <- newNode
        return (n, (n, "NOT") : nodes, (node, n, ()) : edges)

newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i



defaultNodeAnnotate :: (Show v) => LNode (FrozenShareC v) -> [GraphViz.Attribute]
defaultNodeAnnotate (_, FrozenShareC (output, cmaps)) = go output
  where
    go CTrue{}       = "true"
    go CFalse{}      = "false"
    go (CVar _ i)    = show $ extract i varMap
    go (CNot{})      = "NOT"
    go (CAnd{hlc=h}) = maybe "AND" goHLC h
    go (COr{hlc=h})  = maybe "OR" goHLC h

    goHLC (Xor{})    = "XOR"
    goHLC (Onlyif{}) = go (output{ hlc=Nothing })
    goHLC (Iff{})    = "IFF"

    extract code f =
        IntMap.findWithDefault (error $ "shareGraph: unknown code: " ++ show code)
        code
        (f cmaps)

defaultEdgeAnnotate = undefined

dotGraph :: (Graph gr) => gr (FrozenShareC v) (FrozenShareC v) -> DotGraph
dotGraph g = graphToDot g defaultNodeAnnotate defaultEdgeAnnotate


shareGraph :: (DynGraph gr, Eq v, Show v) =>
              FrozenShareC v -> gr (FrozenShareC v) (FrozenShareC v)
shareGraph (FrozenShareC (output, cmaps)) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar _ i) = do
        --v <- extract i varMap
        return (i, [(i, frz c)], [])
    go c@(CTrue _ i)  = return (i, [(i, frz c)], [])
    go c@(CFalse _ i) = return (i, [(i, frz c)], [])
    go c@(CNot _ i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd maybeFrom i) =
        maybe (extract i andMap >>= tupM2 go >>= addKids c) (goHLC c) maybeFrom
    go c@(COr maybeFrom i)  =
        maybe (extract i orMap  >>= tupM2 go >>= addKids c) (goHLC c) maybeFrom

    -- Use the high-level circuit children when displaying.
    goHLC parent (Xor hl hr)    = tupM2 go (hl, hr) >>= addKids parent
    goHLC parent (Onlyif hl hr) = tupM2 go (hl, hr) >>= addKids parent
    goHLC parent (Iff hl hr)    = tupM2 go (hl, hr) >>= addKids parent

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, frz ccode) : (rNode, i, frz ccode) : lEdges ++ rEdges)
    tupM2 f (x, y) = liftM2 (,) (f x) (f y)
    frz ccode = FrozenShareC (ccode, cmaps)
    extract code f = do
        maps <- ask
        return $
          IntMap.findWithDefault (error $ "shareGraph: unknown code: " ++ show code)
          code
          (f maps)

-}

-- ** Circuit simplification

-- | Performs obvious constant propagations.
simplifyCircuit :: TreeC v -> TreeC v
simplifyCircuit l@(TLeaf _) = l
simplifyCircuit TFalse      = TFalse
simplifyCircuit TTrue       = TTrue
simplifyCircuit (TNot t) =
    let t' = simplifyCircuit t
    in case t' of
         TTrue  -> TFalse
         TFalse -> TTrue
         _      -> TNot t'
simplifyCircuit (TAnd l r) =
    let l' = simplifyCircuit l
        r' = simplifyCircuit r
    in case l' of
         TFalse -> TFalse
         TTrue  -> case r' of
           TTrue  -> TTrue
           TFalse -> TFalse
           _      -> r'
         _      -> case r' of
           TTrue -> l'
           TFalse -> TFalse
           _ -> TAnd l' r'
simplifyCircuit (TOr l r) =
    let l' = simplifyCircuit l
        r' = simplifyCircuit r
    in case l' of
         TFalse -> r'
         TTrue  -> TTrue
         _      -> case r' of
           TTrue  -> TTrue
           TFalse -> l'
           _      -> TOr l' r'
simplifyCircuit (TXor l r) =
    let l' = simplifyCircuit l
        r' = simplifyCircuit r
    in case l' of
         TFalse -> r'
         TTrue  -> case r' of
           TFalse -> TTrue
           TTrue  -> TFalse
           _      -> TNot r'
         _      -> TXor l' r'

-- ** Pseudo-boolean circuits (TODO)

-- TODO Want to encode cardinality constraints as circuits, in order to
-- implement a cardinality-based optimisation loop.  This appears to be the
-- easiest route to *good* and correct plans.


-- ** Convert circuit to CNF

-- | Produces a CNF formula that is satisfiable if and only if the input circuit
-- is satisfiable.  /Note that it does not produce an equivalent CNF formula./
-- It is not equivalent in general because the transformation introduces
-- variables into the CNF which were not present as circuit inputs.  (Variables
-- in the CNF correspond to circuit elements.)  Returns equisatisfiable CNF
-- along with the frozen input circuit, and the mapping between the variables of
-- the CNF and the circuit elements.
--
-- The implementation uses the Tseitin transformation, to guarantee that the
-- output CNF formula is linear in the size of the circuit.  Contrast this with
-- the naive DeMorgan-laws transformation which produces an exponential-size CNF
-- formula.
--
-- /TODO/ especially with the sharing-slash-flat representation, I should be
-- able to write this tail-recursively.
--
-- /TODO/ can easily count the number of variables while constructing cnf
toCNF :: (Ord v) => ShareC v -> (CNF, FrozenShareC v, Map Var CCode)
toCNF sc =
    let c@(FrozenShareC (sharedCircuit, circuitMaps)) = runShareC sc
        (cnf, m) = ((`runReader` circuitMaps) . (`runStateT` Map.empty)) $ do
                     (l, theClauses) <- cnfTree sharedCircuit
                     return $ Set.insert (Set.singleton l) theClauses
    in ( CNF { numVars =   Set.fold max 1
                         . Set.map (Set.fold max 1)
                         . Set.map (Set.map (unVar . var))
                         $ cnf
             , numClauses = Set.size cnf
             , clauses = Set.map Foldable.toList cnf }
       , c
       , m )
  where
    -- Invariant: returns (l, c) where l is the literal corresponding to the
    -- circuit input, and {l} U c is CNF equisatisfiable with the input
    -- circuit.
    cnfTree c@(CVar _ i)   = store (V i) c >> return (L i, Set.empty)
    cnfTree c@(CTrue _ i)  =
        store (V i) c >> return (L i, Set.singleton . Set.singleton $ L i)
    cnfTree c@(CFalse _ i) =
        store (V i) c >> return (L i, Set.fromList [Set.singleton (negate (L i))])

    -- x <-> -y
    --   <-> (-x, -y) & (y, x)
    cnfTree c@(CNot _ i) = do
        store (V i) c
        eTree <- extract i notMap
        (eLit, eCnf) <- cnfTree eTree
        let notLit = L i
        return
          ( notLit
          , Set.fromList [ Set.fromList [negate notLit, negate eLit]
                         , Set.fromList [eLit, notLit] ]
            `Set.union` eCnf )

    -- x <-> (y | z)
    --   <-> (-y, x) & (-z, x) & (-x, y, z)
    cnfTree c@(COr _ i) = do
        store (V i) c
        (l, r) <- extract i orMap
        (lLit, lCnf) <- cnfTree l
        (rLit, rCnf) <- cnfTree r
        let orLit = L i
        return
          ( orLit
          , Set.fromList [ Set.fromList [negate lLit, orLit]
                         , Set.fromList [negate rLit, orLit]
                         , Set.fromList [negate orLit, lLit, rLit] ]
            `Set.union` lCnf `Set.union` rCnf )
              
    -- x <-> (y & z)
    --   <-> (-x, y), (-x, z) & (-y, -z, x)
    cnfTree c@(CAnd _ i) = do
        store (V i) c
        (l, r) <- extract i andMap
        (lLit, lCnf) <- cnfTree l
        (rLit, rCnf) <- cnfTree r
        let andLit = L i
        return
          ( andLit
          , Set.fromList [ Set.fromList [negate andLit, lLit]
                         , Set.fromList [negate andLit, rLit]
                         , Set.fromList [negate lLit, negate rLit, andLit] ]
            `Set.union` lCnf `Set.union` rCnf)

    store v ccode  = modify $ Map.insert v ccode
    extract code f =
        (IntMap.findWithDefault (error $ "toCNF: unknown code: " ++ show code)
           code . f) `liftM` ask

