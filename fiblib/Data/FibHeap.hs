{-# LANGUAGE   MultiParamTypeClasses
             , FlexibleInstances
             , EmptyDataDecls #-}

module Data.FibHeap
#ifndef TESTING
    ( Heap(..)
    , HeapPolicy(..)
    , empty
    , peek
    , insert
    , decreaseKey
    , datum
    , key
    , focusElement
    )
#endif
    where

-- import Control.Arrow ( (&&&) )
import Control.Monad ( MonadPlus(..), guard )
import Prelude hiding ( foldr, min )
-- import Data.Sequence ( Seq, (<|), (|>), (><), ViewL(..), ViewR(..) )
import Data.Foldable
-- import Data.IntMap (IntMap)
import Data.Tree
import Data.Maybe ( isJust )
-- import qualified Data.List as List
import qualified Prelude as Prelude
import qualified Data.Sequence as Seq
import qualified Data.IntMap as IntMap


-- * Forest cursor

data Path a = Point { left   :: Forest a -- ^ 1st left thing on front
                    , right  :: Forest a -- ^ 1st right thing on front
                    , up     :: Maybe (a, Path a)
                    -- ^ The label of the parent and a path up.
                    }
              deriving (Show, Eq)

emptyPath :: Path a
emptyPath = Point [] [] Nothing

data Cursor a = EmptyC
              | Cursor { focus   :: Tree a
                       , context :: Path a }
                deriving Show

closeCursor :: Cursor a -> Forest a
closeCursor EmptyC = []
closeCursor c@(Cursor t p) =
    case up p of
      Nothing -> left p ++ [t] ++ right p
      _       -> (closeCursor . focusUp) c
          

focusElement :: Cursor a -> a
focusElement EmptyC = error "focusElement: empty"
focusElement c = (rootLabel . focus) c

focusLeft, focusRight, focusUp, focusDown :: Cursor a -> Cursor a

focusLeft EmptyC = error "focusLeft: empty"
focusLeft c@(Cursor t p) = case p of
    Point (l:ls) rs u -> Cursor l (Point ls (t:rs) u)
    _                 -> c

focusRight EmptyC = error "focusLeft: empty"
focusRight c@(Cursor t p) = case p of
    Point ls (r:rs) u -> Cursor r (Point (t:ls) rs u)
    _                 -> c

focusUp EmptyC = error "focusLeft: empty"
focusUp c@(Cursor t p) = case p of
    Point { up = Nothing }     -> c
    Point ls rs (Just (p', u)) -> Cursor (Node p' (reverse ls ++ t : rs)) u

-- | Focus on the leftmost subtree of current focus.  If no such, returns
-- cursor unmodified.
focusDown EmptyC = error "focusLeft: empty"
focusDown c@(Cursor t p) = case t of
    Node l (t1:ts) -> Cursor t1 (Point [] ts (Just (l, p)))
    _              -> c

-- | Replace the focused tree, creating new if necessary.
frobFocus :: Tree a -> Cursor a -> Cursor a
frobFocus x EmptyC = Cursor x emptyPath
frobFocus x (Cursor _ p) = Cursor x p

modifyFocus :: Cursor a -> (Tree a -> Tree a) -> Cursor a
modifyFocus EmptyC _       = EmptyC
modifyFocus (Cursor t p) f = Cursor (f t) p

-- | Insert a new element at the focus, moving focused element to right.  If
-- the initial focus was empty, focuses on the new element.
insertFocus :: Tree a -> Cursor a -> Cursor a
insertFocus x EmptyC = Cursor x emptyPath
insertFocus x (Cursor t p) = case p of
    Point ls rs u -> Cursor x (Point ls (t:rs) u)

-- | Insert element at immediate right of focus, or at focus if empty.
insertRight :: Tree a -> Cursor a -> Cursor a
insertRight x EmptyC = Cursor x emptyPath
insertRight x (Cursor t p) = case p of
    Point ls rs u -> Cursor t (Point ls (x:rs) u)

insertWithRight :: Tree a
                -> (Tree a -> Tree a -> (Tree a, Tree a))
                -- ^ /existing/ -> /new/ -> (/focus/, /right/)
                -> Cursor a -> Cursor a
insertWithRight x _ EmptyC = Cursor x emptyPath
insertWithRight x f (Cursor t (Point ls rs u)) = Cursor t' (Point ls (r':rs) u)
  where (t', r') = f t x

-- | Delete the focus subtree and try to move right, then left, then up, and
-- finally to the empty cursor, in that order.
delete :: Cursor a -> Cursor a
delete EmptyC = error "delete: empty"
delete (Cursor _ p) = case p of
    Point ls (r:rs) u         -> Cursor r (Point ls rs u)
    Point (l:ls) [] u         -> Cursor l (Point ls [] u)
    Point [] [] (Just (x, p')) -> Cursor (Node x []) p'
    Point [] [] Nothing       -> EmptyC

-- | Delete focused element and move focus to parent, if any.  If no parent,
-- returns empty cursor.
deleteUp :: Cursor a -> Cursor a
deleteUp EmptyC = error "deleteUp: empty"
deleteUp (Cursor t p) = case p of
    Point _ _ Nothing          -> EmptyC
    Point ls rs (Just (p', u)) -> Cursor (Node p' (reverse ls ++ t : rs)) u


-- * Heap implementation

-- | A heap policy indicates which elements are closer to the `min' in the
-- heap.  If @x@ is less than @y@ according to `heapCompare', @x@ is closer to
-- the `min' than @y@.
class (Eq a) => HeapPolicy p a where
    -- | The minimum possible value.  This is used to delete elements (by
    -- decreasing their key to the minimum possible value, then extracting the
    -- min).
    heapMin     :: a

    -- | Compare elements for the heap.  Lesser elements are closer to the
    -- `min'.
    heapCompare :: p -- ^ /Must not be evaluated./
                -> a -> a -> Ordering

-- Convenience for comparing nodes?
instance (HeapPolicy p k) => Ord (Info p k a) where
    compare n n' = heapCompare (policy n) (key n) (key n')

data Heap p k a = H
    { min       :: Cursor (Info p k a)
    , size      :: Int                 -- ^ Number of elements in the heap.
    , numMarked :: Int }
                  deriving Show
    
-- data Node p k a = N
--     { key    :: k
--     , parent :: Zipper (Node p k a) -- ^ Focused on parent node.
--     , child  :: Zipper (Node p k a) -- ^ Focused on child node.
--     , mark   :: Bool
--     , degree :: Int
--     , datum  :: a }
--                 deriving Show

-- | Info kept for each node in the tree.
data Info p k a = Info
    { key    :: k
    , mark   :: Bool            -- ^ Has this node lost a child since the last
                                -- time it was made the child of another node?
    , datum  :: a }
                  deriving Show

instance (Eq k) => Eq (Info p k a) where
    i == i' = key i == key i'


policy :: Info p k a -> p
policy = const undefined

-- * Operations

-- | The empty Fibonacci heap.
empty :: HeapPolicy p k => Heap p k a
empty = H { min       = EmptyC
          , size      = 0
          , numMarked = 0 }

peek :: Heap p k a -> a
peek = datum . focusElement . min

-- | Insert given value with given key into the heap.
insert :: HeapPolicy p k => (k, a) -> Heap p k a -> Heap p k a
insert (k, v) heap = heap' { min = insertMinimumFocus infoNode (min heap') }
  where heap'    = heap{ size = size heap + 1 }
        info     = Info { key = k, mark = False, datum = v }
        infoNode = Node info []

-- | Insert the `Info' into the cursor and focus on a (possibly new) minimum
-- element.
insertMinimumFocus :: Ord a => Tree a -> Cursor a -> Cursor a
insertMinimumFocus node tree = insertWithRight node focusOnMin tree
    where
      focusOnMin n n' = (argmin rootLabel n n', argmax rootLabel n n')


-- | Extract the minimum node from the heap, as determined by `heapCompare'.
--
-- N.B. This function is /not total/: if the heap is empty, throws an error.

extractMin :: HeapPolicy p k => Heap p k a -> (Cursor (Info p k a), Heap p k a)
extractMin heap = case min heap of
    EmptyC -> error "Data.FibHeap.extractMin: empty heap"
    c@(Cursor t _) ->
        ( c
        , heap { min  = consolidate collapsedCursor
               , size = size heap - 1 } )
        where
          -- Add child trees of min as siblings of `c'.
          collapsedCursor = foldl' (flip insertRight) (delete c) (subForest t)


-- In order to use decreaseKey properly, we need to find the cursor for a node
-- that's already in the heap.  We can do this with a worst-case-linear-time
-- search of the heap-ordered trees.  If in the Heap record we keep around the
-- set of items in the heap, then discovering *that* the item is in the heap
-- takes O(log n) time and then linear time to find it.  If we keep a map of
-- unique item identifiers to cursors into the heap, we can recover the
-- cursors in O(log n) time, but we have to update these cursors all the
-- freaking time.  Ugh.

-- Cursor must be non-empty.
decreaseKey :: HeapPolicy p k => Heap p k a -> Cursor (Info p k a) -> k
            -> Heap p k a
decreaseKey heap nodeCursor newKey =
    case newKey `compareKeys` (key . focusElement) nodeCursor of
      GT -> error "Data.FibHeap.decreaseKey: newKey too big"
      _  -> let (Cursor t _) = nodeCursor
            in if (isJust . up . context) nodeCursor then
                   -- at root level, so focus in the minimum of current & min
                   case rootLabel t `compare` (focusElement . min) heap of
                     LT -> heap { min = nodeCursorNewKey }
                     _  -> heap
               else -- not at root level, cut/cascading up to new min
                   heap { min = (undelayCursor . cascadingCut . cut . delayCursor)
                                nodeCursorNewKey }
  where
    compareKeys      = heapCompare (policy (focusElement nodeCursor))
    nodeCursorNewKey =
        frobFocus (focus nodeCursor
                   `modifyRootLabel` (\info -> info { key = newKey }))
        nodeCursor

modifyRootLabel :: Tree a -> (a -> a) -> Tree a
modifyRootLabel t f = t { rootLabel = f (rootLabel t) }


-- | The elements of the forest are elements that belong as siblings of the
-- topmost trees in the tree represented by the cursor.
type DelayedRootlistCursor a = (Forest a, Cursor a)
delayCursor :: Cursor a -> DelayedRootlistCursor a
delayCursor c = ([], c)

undelayCursor :: (Ord a) => DelayedRootlistCursor a -> Cursor a
undelayCursor (roots, c) = foldl' (flip insertMinimumFocus) c roots

-- | @cut c@ removes focus of @c@ and puts it in the (delayed) root list of
-- the tree.
-- 
-- Precondition: The input cursor focus element must have a parent.
cut :: DelayedRootlistCursor (Info p k a) -> DelayedRootlistCursor (Info p k a)
cut c@(_, EmptyC) = c
cut (roots, c) =
    ( focus c `modifyRootLabel` (\info -> info { mark = False }) : roots
    , deleteUp c )

cascadingCut :: DelayedRootlistCursor (Info p k a) 
             -> DelayedRootlistCursor (Info p k a)
cascadingCut d@(_, EmptyC) = d
cascadingCut d@(roots, c) =
    if (isJust . up . context) c then
        if (not . mark . focusElement) c then
             ( roots
             , modifyFocus c (`modifyRootLabel` (\info -> info { mark = True })) )
        else cut d
    else d

-- ** Heap consolidation

consolidate :: HeapPolicy p k => Cursor (Info p k a) -> Cursor (Info p k a)
consolidate = undefined
-- at the end we want:
--  1. exactly one tree of each degree in the root list
--  2. the min to be right
-- consolidate heap = undefined
--     where degMap = foldr (flip linkByDegree) IntMap.empty (min heap)

-- | @linkByDegree map nz@ links @nz@ with node in @map@ which has same degree
-- (if any), and does so recursively, returning a new map.

-- linkByDegree :: HeapPolicy p k =>
--                 IntMap (Node p k a) -- ^ Invariant: if @i@ maps to @n@ in this
--                                     -- map, then @degree n == i@.
--              -> Node p k a
--              -> IntMap (Node p k a)
-- linkByDegree degMap node =
--     if IntMap.member d degMap then
--          linkByDegree degMapLinked linkedNodeZ
--     else IntMap.insert d node degMap
--   where d = degree node
--         -- foci of existingNodeZ and nodeZ have same degree.
--         existingNode = degMap IntMap.! d
--         linkedNodeZ = if node < existingNode then
--                           link existingNode node
--                       else link node existingNode
--         degMapLinked =
--             (IntMap.insert (degree (focus linkedNodeZ)) linkedNodeZ
--              . IntMap.delete (degree node))
--             degMap
    
    


-- ** Helpers

argmax :: (Ord b) => (a -> b) -> a -> a -> a
{-# INLINE argmax #-}
argmax f x y = if f x > f y then x else y

argmin :: (Ord b) => (a -> b) -> a -> a -> a
{-# INLINE argmin #-}
argmin f x y = if f x < f y then x else y

-- | Length of `subForest' of tree.
degree :: Tree a -> Int
degree (Node _ ts) = length ts


findSplit = undefined

-- dfsForest pred [] = Nothing
-- dfsForest pred (t:ts) =
--     if (pred . rootLabel) t then Just t
--     else  

dfsCursor _ EmptyC = Nothing
dfsCursor pred c@(Cursor t p@(Point ls rs _)) = 
    (guard ((pred . rootLabel) t) >> return c)
    `mplus` (guard (null (subForest t)) >> dfsCursor pred (focusDown c))
    `mplus` foldr mplus mzero (map (dfsCursor pred) (rights c))
  where 
    rights (Cursor { context = (Point { right = [] }) }) = []
    rights c = focusRight c : rights (focusRight c)
      
