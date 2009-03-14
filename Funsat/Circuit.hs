

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
    , CastCircuit(..)

    -- ** Explicit sharing circuit
    , ShareC(..)
    , FrozenShareC(..)
    , CircuitHash
    , CCode(..)
    , CMaps(..)
    , emptyCMaps

    -- ** Explicit tree circuit
    , TreeC(..)
    , foldTreeC

    -- *** Circuit simplification
    , simplifyCircuit

    -- ** Explicit graph circuit
    , GraphC
    , runGraphC
    , shareGraph
    , NodeType(..)

    -- ** Circuit evaluator
    , BEnv
    , EvalC(..)
    , runEvalC

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


import Control.Monad.Reader
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Data.Graph.Inductive.Graph( DynGraph, Graph, LNode )
import Data.Graph.Inductive.Tree()
import Data.IntMap( IntMap )
import Data.List( nub )
import Data.Map( Map )
import Data.Maybe()
import Data.Ord()
import Funsat.Types ( CNF(..), Lit(..), Var(..), var )
import Prelude hiding( not, and, or )

import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Prelude as Prelude



-- * Circuit representation


-- | A class representing a grammar for logical circuits.  Default
-- implemenations are indicated.
class Circuit repr where
    true  :: (Ord var, Show var) => repr var
    false :: (Ord var, Show var) => repr var
    input :: (Ord var, Show var) => var -> repr var
    not   :: (Ord var, Show var) => repr var -> repr var

    -- | Defined as @`and' p q = not (not p `or` not q)@.
    and   :: (Ord var, Show var) => repr var -> repr var -> repr var
    and p q = not (not p `or` not q)

    -- | Defined as @`or' p q = not (not p `and` not q)@.
    or    :: (Ord var, Show var) => repr var -> repr var -> repr var
    or p q = not (not p `and` not q)

    -- | If-then-else circuit.  @ite c t e@ returns a circuit that evaluates to
    -- @t@ when @c@ evaluates to true, and @e@ otherwise.
    --
    -- Defined as @(c `and` t) `or` (not c `and` f)@.
    ite :: (Ord var, Show var) => repr var -> repr var -> repr var -> repr var
    ite c t f = (c `and` t) `or` (not c `and` f)

    -- | Defined as @`onlyif' p q = not p `or` q@.
    onlyif :: (Ord var, Show var) => repr var -> repr var -> repr var
    onlyif p q = not p `or` q

    -- | Defined as @`iff' p q = (p `onlyif` q) `and` (q `onlyif` p)@.
    iff :: (Ord var, Show var) => repr var -> repr var -> repr var
    iff p q = (p `onlyif` q) `and` (q `onlyif` p)

    -- | Defined as @`xor' p q = (p `or` q) `and` not (p `and` q)@.
    xor :: (Ord var, Show var) => repr var -> repr var -> repr var
    xor p q = (p `or` q) `and` not (p `and` q)

-- | Instances of `CastCircuit' admit converting on circuit representation to
-- another.
class CastCircuit c where
    castCircuit :: (Circuit cOut, Ord var, Show var) => c var -> cOut var



-- ** Explicit sharing circuit

-- The following business is for elimination of common subexpressions from
-- boolean functions.  Part of conversion to CNF.

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShareC'.
newtype ShareC v = ShareC { unShareC :: State (CMaps v) CCode }

-- | A shared circuit that has already been constructed.
newtype FrozenShareC v = FrozenShareC (CCode, CMaps v) deriving (Eq, Ord, Show, Read)

-- | Reify a sharing circuit.
runShareC :: ShareC v -> FrozenShareC v
runShareC = FrozenShareC . (`runState` emptyCMaps) . unShareC

instance CastCircuit ShareC where
    castCircuit = castCircuit . runShareC

instance CastCircuit FrozenShareC where
    castCircuit (FrozenShareC (code, maps)) = go code
      where
        go (CTrue{})   = true
        go (CFalse{})  = false
        go (CVar i)    = input $ getChildren i varMap
        go (CAnd i)    = uncurry and . go2 $ getChildren i andMap
        go (COr i)     = uncurry or . go2 $ getChildren i orMap
        go (CNot i)    = not . go $ getChildren i notMap
        go (CXor i)    = uncurry xor . go2 $ getChildren i xorMap
        go (COnlyif i) = uncurry onlyif . go2 $ getChildren i onlyifMap
        go (CIff i)    = uncurry iff . go2 $ getChildren i iffMap

        getChildren int codeMap =
            IntMap.findWithDefault (error $ "getChildren: unknown code: " ++ show int)
            int (codeMap maps)
        go2 (x, y) = (go x, go y)

type CircuitHash = Int

-- | A `CCode' represents a circuit element for `ShareC' circuits.  A `CCode' is
-- a flattened tree node which has been assigned a unique number in the
-- corresponding map inside `CMaps', which indicates children, if any.
--
-- For example, @CAnd i@ has the two children of the tuple @lookup i (andMap
-- cmaps)@ assuming @cmaps :: CMaps v@.
data CCode = CTrue   { circuitHash :: !CircuitHash }
           | CFalse  { circuitHash :: !CircuitHash }
           | CVar    { circuitHash :: !CircuitHash }
           | CAnd    { circuitHash :: !CircuitHash }
           | COr     { circuitHash :: !CircuitHash }
           | CNot    { circuitHash :: !CircuitHash }
           | CXor    { circuitHash :: !CircuitHash }
           | COnlyif { circuitHash :: !CircuitHash }
           | CIff    { circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show, Read)

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
    , notMap    :: IntMap CCode
    , xorMap    :: IntMap (CCode, CCode)
    , onlyifMap :: IntMap (CCode, CCode)
    , iffMap    :: IntMap (CCode, CCode) }
               deriving (Eq, Ord, Show, Read)

-- | A `CMaps' with an initial `hashCount' of 1.
emptyCMaps :: CMaps v
emptyCMaps = CMaps
    { hashCount = 1
    , trueInt   = Nothing
    , falseInt  = Nothing
    , varMap    = IntMap.empty
    , andMap    = IntMap.empty
    , orMap     = IntMap.empty
    , notMap    = IntMap.empty
    , xorMap    = IntMap.empty
    , onlyifMap = IntMap.empty
    , iffMap    = IntMap.empty }

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
                     let c = CTrue i
                     modify $ \s -> s{ hashCount = succ i, trueInt = Just c }
                     return c
                 Just c -> return c
    false = ShareC $ do
               ti <- gets falseInt
               case ti of
                 Nothing -> do
                     i <- gets hashCount
                     let c = CFalse i
                     modify $ \s -> s{ hashCount = succ i, falseInt = Just c }
                     return c
                 Just c -> return c
    input v = ShareC $ recordC CVar varMap (\s e -> s{ varMap = e }) v
    and e1 e2 = ShareC $ do
                    hl <- unShareC e1
                    hr <- unShareC e2
                    recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)
    or  e1 e2 = ShareC $ do
                    hl <- unShareC e1
                    hr <- unShareC e2
                    recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)
    not e = ShareC $ do
                h <- unShareC e
                recordC CNot notMap (\s e' -> s{ notMap = e' }) h
    xor l r = ShareC $ do
                  hl <- unShareC l ; hr <- unShareC r
                  recordC CXor xorMap (\s e' -> s{ xorMap = e' }) (hl, hr)
{-    iff l r = ShareC $ do
                  hl <- unShareC l ; hr <- unShareC r
                  let from = Iff hl hr
                  liftM (\c -> c{ hlc = Just from }) . unShareC $
                        (l `onlyif` r) `and` (r `onlyif` l)
    onlyif l r = ShareC $ do
                     hl <- unShareC l ; hr <- unShareC r
                     let from = Onlyif hl hr
                     liftM (\c -> c{ hlc = Just from }) . unShareC $
                           not l `or` r-}
              

-- ** Explicit tree circuit

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.
data TreeC v = TTrue
             | TFalse
             | TLeaf v
             | TAnd (TreeC v) (TreeC v)
             | TOr  (TreeC v) (TreeC v)
             | TXor (TreeC v) (TreeC v)
             | TNot (TreeC v)
               deriving (Show)

foldTreeC :: (t -> v -> t) -> t -> TreeC v -> t
foldTreeC _ i TTrue        = i
foldTreeC _ i TFalse       = i
foldTreeC f i (TLeaf v)    = f i v
foldTreeC f i (TAnd t1 t2) = foldTreeC f (foldTreeC f i t1) t2
foldTreeC f i (TOr t1 t2)  = foldTreeC f (foldTreeC f i t1) t2
foldTreeC f i (TNot t)     = foldTreeC f i t
foldTreeC f i (TXor t1 t2) = foldTreeC f (foldTreeC f i t1) t2

instance Circuit TreeC where
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot
    xor   = TXor

instance CastCircuit TreeC where
    castCircuit TTrue        = true
    castCircuit TFalse       = false
    castCircuit (TLeaf l)    = input l
    castCircuit (TAnd t1 t2) = and (castCircuit t1) (castCircuit t2)
    castCircuit (TOr t1 t2)  = or (castCircuit t1) (castCircuit t2)
    castCircuit (TXor t1 t2) = xor (castCircuit t1) (castCircuit t2)
    castCircuit (TNot t)     = not (castCircuit t)

-- ** Circuit evaluator

type BEnv v = Map v Bool

-- | A circuit evaluator, that is, a circuit represented as a function from
-- variable values to booleans.
newtype EvalC v = EvalC { unEvalC :: BEnv v -> Bool }

-- | Evaluate a circuit given inputs.
runEvalC :: BEnv v -> EvalC v -> Bool
runEvalC = flip unEvalC

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

-- | A circuit type that constructs a `Graph' representation.  This is useful
-- for visualising circuits, for example using the @graphviz@ package.
newtype GraphC v = GraphC
    { unGraphC :: State Graph.Node (Graph.Node,
                                    [Graph.LNode (NodeType v)],
                                    [Graph.LEdge ()]) }

-- | Node type labels for graphs.
data NodeType v = NInput v
                | NTrue
                | NFalse
                | NAnd
                | NOr
                | NNot
                | NXor
                | NIff
                | NOnlyIf
                  deriving (Eq, Ord, Show, Read)

runGraphC :: (DynGraph gr) => GraphC v -> gr (NodeType v) ()
runGraphC graphBuilder =
    let (_, nodes, edges) = evalState (unGraphC graphBuilder) 1
    in Graph.mkGraph nodes edges

instance Circuit GraphC where
    input v = GraphC $ do
        n <- newNode
        return $ (n, [(n, NInput v)], [])

    true = GraphC $ do
        n <- newNode
        return $ (n, [(n, NTrue)], [])

    false = GraphC $ do
        n <- newNode
        return $ (n, [(n, NFalse)], [])

    not gs = GraphC $ do
        (node, nodes, edges) <- unGraphC gs
        n <- newNode
        return (n, (n, NNot) : nodes, (node, n, ()) : edges)

    and    = binaryNode NAnd
    or     = binaryNode NOr
    xor    = binaryNode NXor
    iff    = binaryNode NIff
    onlyif = binaryNode NOnlyIf

binaryNode :: NodeType v -> GraphC v -> GraphC v -> GraphC v
{-# INLINE binaryNode #-}
binaryNode ty l r = GraphC $ do
        (lNode, lNodes, lEdges) <- unGraphC l
        (rNode, rNodes, rEdges) <- unGraphC r
        n <- newNode
        return (n, (n, ty) : lNodes ++ rNodes,
                   (lNode, n, ()) : (rNode, n, ()) : lEdges ++ rEdges)


newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i


{-
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

-}

-- | Given a frozen shared circuit, construct a `DynGraph' that exactly
-- represents it.  Useful for debugging constraints generated as `ShareC'
-- circuits.
shareGraph :: (DynGraph gr, Eq v, Show v) =>
              FrozenShareC v -> gr (FrozenShareC v) (FrozenShareC v)
shareGraph (FrozenShareC (output, cmaps)) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = do
        --v <- extract i varMap TODO
        return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c

--     -- Use the high-level circuit children when displaying.
--     goHLC parent (Xor hl hr)    = tupM2 go (hl, hr) >>= addKids parent
--     goHLC parent (Onlyif hl hr) = tupM2 go (hl, hr) >>= addKids parent
--     goHLC parent (Iff hl hr)    = tupM2 go (hl, hr) >>= addKids parent

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
                     (l, theClauses) <- toCNF' sharedCircuit
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
    -- Returns (l :: Lit, c :: Set Clause) where {l} U c is CNF equisatisfiable
    -- with the input circuit.
    toCNF' c@(CVar i)   = store (V i) c >> return (L i, Set.empty)
    toCNF' c@(CTrue i)  =
        store (V i) c >> return (L i, Set.singleton . Set.singleton $ L i)
    toCNF' c@(CFalse i) =
        store (V i) c >> return (L i, Set.fromList [Set.singleton (negate (L i))])

    -- x <-> -y
    --   <-> (-x, -y) & (y, x)
    toCNF' c@(CNot i) = do
        store (V i) c
        eTree <- extract i notMap
        (eLit, eCnf) <- toCNF' eTree
        let notLit = L i
        return
          ( notLit
          , Set.fromList [ Set.fromList [negate notLit, negate eLit]
                         , Set.fromList [eLit, notLit] ]
            `Set.union` eCnf )

    -- x <-> (y | z)
    --   <-> (-y, x) & (-z, x) & (-x, y, z)
    toCNF' c@(COr i) = do
        store (V i) c
        (l, r) <- extract i orMap
        (lLit, lCnf) <- toCNF' l
        (rLit, rCnf) <- toCNF' r
        let orLit = L i
        return
          ( orLit
          , Set.fromList [ Set.fromList [negate lLit, orLit]
                         , Set.fromList [negate rLit, orLit]
                         , Set.fromList [negate orLit, lLit, rLit] ]
            `Set.union` lCnf `Set.union` rCnf )
              
    -- x <-> (y & z)
    --   <-> (-x, y), (-x, z) & (-y, -z, x)
    toCNF' c@(CAnd i) = do
        store (V i) c
        (l, r) <- extract i andMap
        (lLit, lCnf) <- toCNF' l
        (rLit, rCnf) <- toCNF' r
        let andLit = L i
        return
          ( andLit
          , Set.fromList [ Set.fromList [negate andLit, lLit]
                         , Set.fromList [negate andLit, rLit]
                         , Set.fromList [negate lLit, negate rLit, andLit] ]
            `Set.union` lCnf `Set.union` rCnf )

    -- record that var v maps to circuit element ccode
    store v ccode  = modify $ Map.insert v ccode
    extract code f =
        (IntMap.findWithDefault (error $ "toCNF: unknown code: " ++ show code)
           code . f) `liftM` ask

