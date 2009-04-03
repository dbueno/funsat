

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
    , Shared(..)
    , FrozenShared(..)
    , CircuitHash
    , CCode(..)
    , CMaps(..)
    , emptyCMaps

    -- ** Explicit tree circuit
    , Tree(..)
    , foldTree

    -- *** Circuit simplification
    , simplifyCircuit

    -- ** Explicit graph circuit
    , Graph
    , runGraph
    , shareGraph
    , NodeType(..)

    -- ** Circuit evaluator
    , BEnv
    , Eval(..)
    , runEval

    -- ** Convert circuit to CNF
    , CircuitProblem(..)
    , toCNF
    , projectCircuitSolution
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
import Data.Bimap( Bimap )
import Data.Graph.Inductive.Graph( LNode )
import Data.Graph.Inductive.Tree()
import Data.IntMap( IntMap )
import Data.List( nub )
import Data.Map( Map )
import Data.Maybe()
import Data.Ord()
import Data.Set( Set )
import Funsat.Types( CNF(..), Lit(..), Var(..), var, lit, Solution(..), litSign, litAssignment )
import Prelude hiding( not, and, or )

import qualified Data.Bimap as Bimap
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
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
-- compact representation that facilitates converting to CNF.  See `runShared'.
newtype Shared v = Shared { unShared :: State (CMaps v) CCode }

-- | A shared circuit that has already been constructed.
data FrozenShared v = FrozenShared !CCode !(CMaps v) deriving (Eq, Ord, Show, Read)

-- | Reify a sharing circuit.
runShared :: Shared v -> FrozenShared v
runShared = uncurry FrozenShared . (`runState` emptyCMaps) . unShared

instance CastCircuit Shared where
    castCircuit = castCircuit . runShared

instance CastCircuit FrozenShared where
    castCircuit (FrozenShared code maps) = go code
      where
        go (CTrue{})     = true
        go (CFalse{})    = false
        go c@(CVar{})    = input $ getChildren c (varMap maps)
        go c@(CAnd{})    = uncurry and . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = uncurry or . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = not . go $ getChildren c (notMap maps)
        go c@(CXor{})    = uncurry xor . go2 $ getChildren c (xorMap maps)
        go c@(COnlyif{}) = uncurry onlyif . go2 $ getChildren c (onlyifMap maps)
        go c@(CIff{})    = uncurry iff . go2 $ getChildren c (iffMap maps)

        go2 = (go `onTup`)

getChildren :: CCode -> IntMap v -> v
getChildren code codeMap =
            IntMap.findWithDefault (error $ "getChildren: unknown code: " ++ show code)
            (circuitHash code) codeMap

type CircuitHash = Int

-- | A `CCode' represents a circuit element for `Shared' circuits.  A `CCode' is
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
-- the `Circuit' class.  See `Shared'.
data CMaps v = CMaps
    { hashCount :: [CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.

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
    { hashCount = [1 ..]
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
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (IntMap.insert c x (prj s))
            put s'
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ lookupv x (prj s)

instance Circuit Shared where
    true = Shared $ do
               ti <- gets trueInt
               case ti of
                 Nothing -> do
                     i:is <- gets hashCount
                     let c = CTrue i
                     modify $ \s -> s{ hashCount = is, trueInt = Just c }
                     return c
                 Just c -> return c
    false = Shared $ do
               ti <- gets falseInt
               case ti of
                 Nothing -> do
                     i:is <- gets hashCount
                     let c = CFalse i
                     modify $ \s -> s{ hashCount = is, falseInt = Just c }
                     return c
                 Just c -> return c
    input v = Shared $ recordC CVar varMap (\s e -> s{ varMap = e }) v
    and e1 e2 = Shared $ do
                    hl <- unShared e1
                    hr <- unShared e2
                    recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)
    or  e1 e2 = Shared $ do
                    hl <- unShared e1
                    hr <- unShared e2
                    recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)
    not e = Shared $ do
                h <- unShared e
                recordC CNot notMap (\s e' -> s{ notMap = e' }) h
    xor l r = Shared $ do
                  hl <- unShared l ; hr <- unShared r
                  recordC CXor xorMap (\s e' -> s{ xorMap = e' }) (hl, hr)
    iff l r = Shared $ do
                  hl <- unShared l ; hr <- unShared r
                  recordC CIff iffMap (\s e' -> s{ iffMap = e' }) (hl, hr)
    onlyif l r = Shared $ do
                    hl <- unShared l ; hr <- unShared r
                    recordC COnlyif onlyifMap (\s e' -> s{ onlyifMap = e' }) (hl, hr)

-- ** Explicit tree circuit

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.
data Tree v = TTrue
             | TFalse
             | TLeaf v
             | TAnd (Tree v) (Tree v)
             | TOr  (Tree v) (Tree v)
             | TXor (Tree v) (Tree v)
             | TNot (Tree v)
               deriving (Show)

foldTree :: (t -> v -> t) -> t -> Tree v -> t
foldTree _ i TTrue        = i
foldTree _ i TFalse       = i
foldTree f i (TLeaf v)    = f i v
foldTree f i (TAnd t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TOr t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TNot t)     = foldTree f i t
foldTree f i (TXor t1 t2) = foldTree f (foldTree f i t1) t2

instance Circuit Tree where
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot
    xor   = TXor

instance CastCircuit Tree where
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
newtype Eval v = Eval { unEval :: BEnv v -> Bool }

-- | Evaluate a circuit given inputs.
runEval :: BEnv v -> Eval v -> Bool
runEval = flip unEval

instance Circuit Eval where
    true    = Eval $ const True
    false   = Eval $ const False
    input v = Eval $ \env ->
                      Map.findWithDefault
                        (error $ "Eval: no such var: " ++ show v
                                 ++ " in " ++ show env)
                         v env
    and c1 c2 = Eval (\env -> unEval c1 env && unEval c2 env)
    or  c1 c2 = Eval (\env -> unEval c1 env || unEval c2 env)
    not c     = Eval (\env -> Prelude.not $ unEval c env)

-- ** Graph circuit

-- | A circuit type that constructs a `Graph' representation.  This is useful
-- for visualising circuits, for example using the @graphviz@ package.
newtype Graph v = Graph
    { unGraph :: State Graph.Node (Graph.Node,
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

runGraph :: (G.DynGraph gr) => Graph v -> gr (NodeType v) ()
runGraph graphBuilder =
    let (_, nodes, edges) = evalState (unGraph graphBuilder) 1
    in Graph.mkGraph nodes edges

instance Circuit Graph where
    input v = Graph $ do
        n <- newNode
        return $ (n, [(n, NInput v)], [])

    true = Graph $ do
        n <- newNode
        return $ (n, [(n, NTrue)], [])

    false = Graph $ do
        n <- newNode
        return $ (n, [(n, NFalse)], [])

    not gs = Graph $ do
        (node, nodes, edges) <- unGraph gs
        n <- newNode
        return (n, (n, NNot) : nodes, (node, n, ()) : edges)

    and    = binaryNode NAnd
    or     = binaryNode NOr
    xor    = binaryNode NXor
    iff    = binaryNode NIff
    onlyif = binaryNode NOnlyIf

binaryNode :: NodeType v -> Graph v -> Graph v -> Graph v
{-# INLINE binaryNode #-}
binaryNode ty l r = Graph $ do
        (lNode, lNodes, lEdges) <- unGraph l
        (rNode, rNodes, rEdges) <- unGraph r
        n <- newNode
        return (n, (n, ty) : lNodes ++ rNodes,
                   (lNode, n, ()) : (rNode, n, ()) : lEdges ++ rEdges)


newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i


{-
defaultNodeAnnotate :: (Show v) => LNode (FrozenShared v) -> [GraphViz.Attribute]
defaultNodeAnnotate (_, FrozenShared (output, cmaps)) = go output
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

dotGraph :: (Graph gr) => gr (FrozenShared v) (FrozenShared v) -> DotGraph
dotGraph g = graphToDot g defaultNodeAnnotate defaultEdgeAnnotate

-}

-- | Given a frozen shared circuit, construct a `DynGraph' that exactly
-- represents it.  Useful for debugging constraints generated as `Shared'
-- circuits.
shareGraph :: (G.DynGraph gr, Eq v, Show v) =>
              FrozenShared v -> gr (FrozenShared v) (FrozenShared v)
shareGraph (FrozenShared output cmaps) =
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
    frz ccode = FrozenShared ccode cmaps
    extract code f = do
        maps <- ask
        return $
          IntMap.findWithDefault (error $ "shareGraph: unknown code: " ++ show code)
          code
          (f maps)


-- ** Circuit simplification

-- | Performs obvious constant propagations.
simplifyCircuit :: Tree v -> Tree v
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

-- this data is private to toCNF.
data CNFResult = CP !Lit !(Set (Set Lit))
data CNFState = CNFS{ toCnfVars :: [Var] -- ^ infinite fresh var source
                    , toCnfMap  :: Bimap Var CCode -- ^ record var mapping
                    }
emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , toCnfMap = Bimap.empty }

-- retrieve and create (if necessary) a cnf variable for the given ccode.
--findVar :: (MonadState CNFState m) => CCode -> m Lit
findVar ccode = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    return . lit $ v
      Just v'  -> return . lit $ v'

data CircuitProblem v = CircuitProblem
    { circuitCnf :: CNF
    , circuitFrz :: FrozenShared v
    , circuitCodeMap :: Bimap Var CCode }

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
toCNF :: (Ord v, Show v) => Shared v -> CircuitProblem v
toCNF cIn =
    let c@(FrozenShared sharedCircuit circuitMaps) =
            runShared . removeComplex . runShared $ cIn
        (cnf, m) = ((`runReader` circuitMaps) . (`runStateT` emptyCNFState)) $ do
                     (CP l theClauses) <- toCNF' sharedCircuit
                     return $ Set.insert (Set.singleton l) theClauses
    in CircuitProblem
       { circuitCnf = CNF { numVars =   Set.fold max 1
                          . Set.map (Set.fold max 1)
                          . Set.map (Set.map (unVar . var))
                          $ cnf
                          , numClauses = Set.size cnf
                          , clauses = Set.map Foldable.toList cnf }
       , circuitFrz = c
       , circuitCodeMap = toCnfMap m }
  where
    -- Returns (CP l c) where {l} U c is CNF equisatisfiable with the input
    -- circuit.
    toCNF' c@(CVar{})   = do l <- findVar c
                             return (CP l Set.empty)
    toCNF' c@(CTrue{})  = do
        l <- findVar c
        return (CP l (Set.singleton . Set.singleton $ l))
    toCNF' c@(CFalse{}) = do
        l <- findVar c
        return (CP l (Set.fromList [Set.singleton (negate l)]))

--     -- x <-> -y
--     --   <-> (-x, -y) & (y, x)
    toCNF' c@(CNot i) = do
        notLit <- findVar c
        eTree <- extract i notMap
        (CP eLit eCnf) <- toCNF' eTree
        return
          (CP notLit
              (Set.fromList [ Set.fromList [negate notLit, negate eLit]
                         , Set.fromList [eLit, notLit] ]
              `Set.union` eCnf))

--     -- x <-> (y | z)
--     --   <-> (-y, x) & (-z, x) & (-x, y, z)
    toCNF' c@(COr i) = do
        orLit <- findVar c
        (l, r) <- extract i orMap
        (CP lLit lCnf) <- toCNF' l
        (CP rLit rCnf) <- toCNF' r
        return
          (CP orLit
              (Set.fromList [ Set.fromList [negate lLit, orLit]
                         , Set.fromList [negate rLit, orLit]
                         , Set.fromList [negate orLit, lLit, rLit] ]
              `Set.union` lCnf `Set.union` rCnf))
              
--     -- x <-> (y & z)
--     --   <-> (-x, y), (-x, z) & (-y, -z, x)
    toCNF' c@(CAnd i) = do
        andLit <- findVar c
        (l, r) <- extract i andMap
        (CP lLit lCnf) <- toCNF' l
        (CP rLit rCnf) <- toCNF' r
        return
          (CP andLit
             (Set.fromList [ Set.fromList [negate andLit, lLit]
                         , Set.fromList [negate andLit, rLit]
                         , Set.fromList [negate lLit, negate rLit, andLit] ]
             `Set.union` lCnf `Set.union` rCnf))
        

    extract code f =
        (IntMap.findWithDefault (error $ "toCNF: unknown code: " ++ show code)
           code . f) `liftM` ask

-- removes iff, xor, onlyif, ite
removeComplex :: (Ord v, Show v, Circuit c) => FrozenShared v -> c v
removeComplex (FrozenShared code maps) = go code
  where
  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren c (varMap maps)
  go c@(COr{})  = uncurry or (go `onTup` getChildren c (orMap maps))
  go c@(CAnd{}) = uncurry and (go `onTup` getChildren c (andMap maps))
  go c@(CNot{}) = not . go $ getChildren c (notMap maps)
  go c@(CXor{}) =
      let (l, r) = go `onTup` getChildren c (xorMap maps)
      in (l `or` r) `and` not (l `and` r)
  go c@(COnlyif{}) =
      let (p, q) = go `onTup` getChildren c (onlyifMap maps)
      in not p `or` q
  go c@(CIff{}) =
      let (p, q) = go `onTup` getChildren c (iffMap maps)
      in (not p `or` q) `and` (not q `or` p)

-- (c `and` t) `or` (not c `and` f)

onTup f (x, y) = (f x, f y)

projectCircuitSolution :: (Ord v) => Solution -> CircuitProblem v -> BEnv v
projectCircuitSolution (Sat lits) pblm =
    -- only the lits whose vars are (varMap maps) go to benv
    foldl (\m l -> case IntMap.lookup (litHash l) (varMap maps) of
                     Nothing -> m
                     Just v  -> Map.insert v (litSign l) m)
          Map.empty
          (litAssignment lits)
  where
  (FrozenShared _ maps) = circuitFrz pblm
  litHash l = case Bimap.lookup (var l) (circuitCodeMap pblm) of
                Nothing -> error $ "projectSolution: unknown lit: " ++ show l
                Just code -> circuitHash code

