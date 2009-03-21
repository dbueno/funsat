
-- | Fibonacci heap implementation.
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
import Data.FDList
import Data.Foldable
-- import Data.IntMap (IntMap)
import Data.Tree
import Data.Maybe ( isJust )

-- import qualified Data.List as List
import qualified Prelude as Prelude
import qualified Data.Sequence as Seq
import qualified Data.IntMap as IntMap
import qualified Data.FDList as L


-- * Heap implementation

data Heap k a = H
    { min       :: DList (Info k a)
    , size      :: Int          -- ^ Number of elements in the heap.
    , numMarked :: Int }
                  deriving Show

-- | Info kept for each node in the tree.
data Info k a = Info
    { key    :: k
    , parent :: Maybe (DList (Info k a))
    , child  :: Maybe (DList (Info k a))
    , mark   :: Bool            -- ^ Has this node lost a child since the last
                                -- time it was made the child of another node?
    , datum  :: a }
                  deriving Show

emptyInfo k v = Info{ key = k
                    , parent = Nothing
                    , child = Nothing
                    , mark = False
                    , datum = v }

instance (Eq k) => Eq (Info k a) where
    i == i' = key i == key i'

-- | The empty Fibonacci heap.
empty :: (Ord k) => Heap k a
empty = H { min       = L.empty
          , size      = 0
          , numMarked = 0 }

-- | Returns the min of the heap, if any.
peek :: Ord k => Heap k a -> Maybe a
peek (H{ min = m }) = if L.isEmpty m then Nothing
                      else Just . datum . L.getCurrent $ m

-- * Operations

insert :: (Ord k) => Heap k a -> k -> a -> Heap k a
insert h@(H{ min = m }) k v =
    h{ min  = if not (L.isEmpty m) && k < key (getCurrent m) then
                  moveLeft' l'
              else l'
     , size = succ (size h) }
  where
    l' = insertRight newInfo m
    newInfo = emptyInfo k v

#if 0

-- | Insert given value with given key into the heap.
insert :: HeapPolicy p k => k -> a -> Heap p k a -> Heap p k a
insert (k, v) heap =
    let newMininfo `L.insertRight` min heap

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
      
#endif
