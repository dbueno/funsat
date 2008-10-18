
-- | A zipper data type for managing circular sequences of elements.
-- Internally the @Data.Sequence@ implementation is used, as this gives good
-- time bounds for adding elements to the front and end of a sequence.  This
-- means there is a certain ''strictness penalty'' whose performance impacts
-- I'm not sure of yet.
--
-- A zipper is a way of viewing a sequence.  One element of the sequence is
-- designated the /focus/, and the zipper is said to be /focused on/ this
-- element.  One can view the elements preceding and succeeding the focus
-- element in constant time, wrapping around the ''ends'' if one is reached.
-- (There really is no end; the zipper should be thought of as a ring of
-- elements, like a circular linked list.)
module Data.SequenceZipper where

import Prelude hiding ( foldr, length, foldl )
import Data.Sequence ( Seq, (<|), (|>), (><), ViewL(..), ViewR(..) )
import Data.Foldable
import qualified Data.Sequence as Seq


-- * Circular zipper

-- | Notes:
--
-- * The @Foldable@ instance folds from the focus element down the zipper.
--
-- * The @Functor@ instance uses @Data.Sequence@'s @Functor@ instance to map.
data Zipper a = Empty               -- ^ Represents the empty sequence.
              | Z (Seq a) a (Seq a) -- ^ The element in the middle slot is has
                                    -- the /focus/.
                deriving (Eq)
instance Show a => Show (Zipper a) where
    show Empty = "<empty zipper>"
    show z      = "Z" ++ show (toList z)

-- Traverses from the first element onward.
instance Foldable Zipper where
    foldr f b z =
        case z of
          Empty -> b
          (Z ls x rs) -> foldr f b (Seq.singleton x >< rs >< ls)

instance Functor Zipper where
    fmap f z =
        case z of
          Empty      -> Empty
          (Z ls x rs) -> Z (f `fmap` ls) (f x) (f `fmap` rs)

-- | The empty zipper.
empty :: Zipper a
empty = Empty

-- | A view of the zipper.
view :: Zipper a -> Zipper a
view = id

-- | /O(1)/.  The number of elements in the zipper.
length :: Zipper a -> Int
length Empty       = 0
length (Z ls _ rs) = 1 + Seq.length ls + Seq.length rs

-- | /O(1)/. Whether the zipper contains any elements.
isEmpty :: Zipper a -> Bool
isEmpty Empty = True
isEmpty _      = False

-- | /O(1)/. Create a zipper from one element.
singleton :: a -> Zipper a
singleton x = Z Seq.empty x Seq.empty

-- | /O(1)/. Focus on the element immediately to the right of the current focus.
focusRight :: Zipper a -> Zipper a
focusRight Empty = Empty
focusRight z@(Z ls x rs) =
    case Seq.viewl rs of
      EmptyL ->
          case Seq.viewl ls of
            EmptyL      -> z
            (x' :< ls') -> Z Seq.empty x' (ls' |> x)
      (x' :< rs') -> Z (ls |> x) x' rs'

-- | /O(1)/. Delete the focus element and focus on the element immediately to
-- its right.  Returns `Empty' if the input is empty or has exactly one
-- element.
-- 
-- N.B.: /This function is total.  An empty input is simply ignored./
focusRightDelete :: Zipper a -> Zipper a
focusRightDelete Empty = Empty
focusRightDelete z =
    case focusRight z of
      (Z ls x rs) -> let (ls' :> _) = Seq.viewr ls in Z ls' x rs
      Empty -> error "focusRightDelete: bad results from focusRight"

-- | /O(1)/. Focus on the element immediately to the left of the current
-- focus.
focusLeft :: Zipper a -> Zipper a
focusLeft Empty = Empty
focusLeft z@(Z ls x rs) =
    case Seq.viewr ls of
      EmptyR ->
          case Seq.viewr rs of
            EmptyR -> z
            (rs' :> x') -> Z (x <| rs') x' Seq.empty
      (ls' :> x') -> Z ls' x' (x <| rs)

-- | Splice two zippers such that the resulting zipper's focus is the first
-- zipper's focus. The iteration order is through the first zipper first and
-- the second zipper second.
spliceL :: Zipper a -> Zipper a -> Zipper a
spliceL Empty z = z
spliceL z Empty = z
spliceL (Z as b cs) (Z xs y zs) = Z (as >< xs >< Seq.singleton y >< zs) b cs

-- | @spliceR = flip spliceL@
spliceR :: Zipper a -> Zipper a -> Zipper a
spliceR = flip spliceL

-- | Insert an element at the last position (relative to the focus) of the
-- zipper.
insertLast :: a -> Zipper a -> Zipper a
insertLast x Empty      = singleton x
insertLast x (Z ls f rs) = Z (ls |> x) f rs

-- | Insert an element at the focus location.  Does not clobber the current
-- focus, merely changes focus.
insert :: a -> Zipper a -> Zipper a
insert x Empty      = singleton x
insert x (Z ls f rs) = Z ls x (f <| rs)

-- | Grab the focus element.
--
-- N.B. This function is not total.  It will throw an error if the zipper is
-- empty.
focus :: Zipper a -> a
focus Empty = error "focus: empty zipper"
focus (Z _ x _) = x

-- | Fold over all possible focusings to the right.
zipFoldr :: (Zipper a -> b -> b) -> b -> Zipper a -> b
{-# INLINE zipFoldr #-}
zipFoldr f b z = foldr f b (take (length z) $ iterate focusRight z)

-- | Fold over all possible focusings to the left
zipFoldl :: (b -> Zipper a -> b) -> b -> Zipper a -> b
{-# INLINE zipFoldl #-}
zipFoldl f b z = foldl f b (take (length z) $ iterate focusLeft z)

-- bad 'cause non-total
unzip Empty = error "metpY"
unzip (Z ls x rs) =
    ( x
    , case Seq.viewr ls of
        EmptyR ->
            case Seq.viewl rs of
              EmptyL -> Empty
              (x' :< rs') -> Z Seq.empty x' rs'
        (ls' :> x') -> Z ls' x' rs)

-- | Construct a zipper from a list of elements.  The first element in the
-- input list (if there is one) becomes the focus.
fromList :: [a] -> Zipper a
fromList [] = Empty
fromList l  = (fromSeq . Seq.fromList) l
-- fromListZ (x:xs) = Z [] x (cycle xs)
--  Then focusRight is just tail... but zprev....

-- | See `fromList' and imagine the right thing.
fromSeq :: Seq a -> Zipper a
fromSeq s = case Seq.viewl s of
               EmptyL    -> Empty
               (x :< rs) -> Z Seq.empty x rs


-- * Zipper properties

zEltsRight z@(Z _ x _) = x : zEltsRight (focusRight z)
zEltsLeft z@(Z _ x _) = x : zEltsLeft (focusLeft z)

prop_zip_fromToList (z :: Zipper Int) =
    z == (fromList . toList) z

prop_zip_toFromList (is :: [Int]) =
    is == (toList . fromList) is

-- Singleton zipper always the same element.                        
prop_zip_single (i :: Int) =
    z == focusRight z && focusRight z == focusLeft z
    && z == focusLeft z
    where z = SeqZ.singleton i

-- Left undoes right, and vice versa.
prop_zshift_idempotent (is :: [Int]) =
    z == focusLeft (focusRight z) && z == focusRight (focusLeft z)
  where z = SeqZ.fromList is

-- First element of zipper always head of creation list.
prop_zelements_first (is :: [Int]) =
    trivial (null is) $
    not (null is) ==>
      rights!!0 == is!!0 && lefts!!0 == is!!0
    where rights = zEltsRight (SeqZ.fromList is)
          lefts = zEltsLeft (SeqZ.fromList is)

prop_zipLength (z :: Zipper Int) =
    case z of
      Empty       -> 0 == SeqZ.length z
      (Z ls x rs) -> SeqZ.length z == Seq.length ls + 1 + Seq.length rs

-- Structural invariant on zipper ordering for both Right and Left.
prop_zEltsRight (is :: [Int]) =
    trivial (null is) $
    zelts == drop 1 is
    where zelts = take (length is - 1) $ drop 1 $ zEltsRight (SeqZ.fromList is)

prop_zEltsLeft (is :: [Int]) =
    trivial (null is) $
    zelts == reverse (drop 1 is)
    where zelts =  take (length is - 1) $ drop 1 $ zEltsLeft (SeqZ.fromList is)

prop_zipStructureRight (z :: Zipper Int) =
    case z of
      Empty -> True `trivial` True
      (Z ls x rs) -> property $
           Seq.singleton x >< rs >< ls
           == Seq.fromList (take (SeqZ.length z) (zEltsRight z))

prop_zipStructureLeft (z :: Zipper Int) =
    case z of
      Empty -> True `trivial` True
      (Z ls x rs) -> property $
          Seq.singleton x >< Seq.reverse ls >< Seq.reverse rs
          == Seq.fromList (take (SeqZ.length z) (zEltsLeft z))

-- The folding order starts at the focus element and proceeds rightward.
prop_zip_Foldable (z :: Zipper Int) =
    trivial (isEmpty z) $
    toList z == theList
  where theList = case z of
                    Empty -> []
                    (Z ls x rs) -> [x] ++ toList rs ++ toList ls

prop_zip_functor_id (z :: Zipper Int) =
    trivial (isEmpty z) $
    z == id `fmap` z

prop_zip_functor_fmap (f :: Int -> Int) (g :: Int -> Int) (z :: Zipper Int) =
    trivial (isEmpty z) $
    fmap (f . g) z == (fmap f . fmap g) z

prop_zip_spliceL (z :: Zipper Int) z' =
    trivial (isEmpty z || isEmpty z') $
    toList z ++ toList z' == toList (z `spliceL` z')

prop_zip_spliceR (z :: Zipper Int) z' =
    trivial (isEmpty z || isEmpty z') $
    toList z' ++ toList z == toList (z `spliceR` z')

-- Both splice directions should be consistent.
prop_zip_splices (z :: Zipper Int) z' =
    trivial (isEmpty z || isEmpty z') $
    z' `spliceL` z == z `spliceR` z'

prop_zip_insertLast (i :: Int) z =
    trivial (isEmpty z) $
    i == last (toList (i `insertLast` z))

prop_zip_insert (i :: Int) z =
    trivial (isEmpty z) $
    i == head (toList (i `SeqZ.insert` z))

prop_zipFoldr (z :: Zipper Int) =
    trivial (isEmpty z) $
    if isEmpty z then
      0 == length resultSum
      && toList z == resultFocus
    else
      1 == (length . nub) resultSum
      && toList z == resultFocus
  where resultSum = zipFoldr (\ z' l -> sum (toList z') : l) [] z
        resultFocus = zipFoldr (\ z' l -> focus z' : l) [] z

prop_zipFoldr (z :: Zipper Int) =
    trivial (isEmpty z) $
    [toList z] == nub resultToList
  where resultToList = zipFoldr (\ z' l -> toList z' : l) [] z
