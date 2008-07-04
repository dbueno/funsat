
-- | Records are ubiquitous in haskell code.  When nesting records, updates
-- deep in the structure become onerous.  This topic has come up several times
-- on @haskell-cafe@, and I'm putting in this class what I think is a good
-- solution to the problem that (1) doesn't require learning weird new infix
-- operators (like
-- <http://darcs.haskell.org/record-access/src/Data/Accessor.hs>) and (2)
-- doesn't use template haskell (like
-- <http://hackage.haskell.org/cgi-bin/hackage-scripts/package/data-accessor>).
-- In fact, this is all Haskell98.
--
-- The code is adapted from
-- <http://twan.home.fmf.nl/blog/haskell/overloading-functional-references.details>.
--
-- For example, to use with a record
--
-- > data Person = P { name :: Name }
-- > data Name = N { first :: String, last :: String }
--
-- Normally, if @p@ is a @Person@, one would write the following to update the
-- last name:
--
-- > p{ name = (name p){ last = (last . name $ p) ++ "fhqwgads" } }
--
-- This becomes rapidly cumbersome with longer names, or more nesting, or more
-- complicated updates (what if the value @(last . name $ p)@ is referred to
-- more than once?).  Note also how the code that /performs the update/ is
-- hard to separate from the code that
-- /figures out where to store the update/.  Moreover, each such update
-- must reproduce the code above.
--
-- With this library, one can treat the references involved as first-class,
-- compose them, and use that for update, modularising and in the end
-- requiring less code for updates.
--
-- > personLastNameRef = lastNameRef `compose` nameRef
-- >   where nameRef = ref name (\newName p -> p{ name = newName })
-- >         lastNameRef = ref last (\newLast n -> n{ last = newLast })
-- > update (personLastNameRef :: FRef Person String) (++ "fhqwgads") p
--
-- Note how the /place of the update/ is separated from
-- /the function that performs the update/.
-- This is a clean, reusable, modular separation.
--
-- When using `FRef', references are also reusable.  For example, we can
-- easily extract the last name of a @Person@ using @personLastNameRef@:
--
-- > get personLastNameRef p
module Data.FRef
    ( -- * Reference typeclass
      Ref(..)
    , FRef(..)
      -- * References for built-in types
    , Data.FRef.fst
    , Data.FRef.snd )
    where

import Prelude hiding ( fst, last )
import qualified Prelude

-- | A `Ref' is a composable way of succinctly remembering how to
-- access/update a member of a (possibly-deep) structure.  This is similar to
-- references in ML, which actually do a destructive update.  As can be seen
-- from the signature of `update', ours is not destructive, but applies the
-- update to a given structure in a functional manner.
class Ref r where
    -- | Creates a reference to a value of type @a@ inside a structure of type
    -- @s@ using getter and setter functions.
    ref :: (s -> a) -> (a -> s -> s) -> r s a

    -- | Composes two references to allow ''deeper'' access into the second
    -- structure, @t@.
    compose :: r s a -> r t s -> r t a

    -- | Apply a change to the referenced value in a structure.
    update :: r s a -> (a -> a) -> s -> s

-- instance Ref (->) where
--     ref g s = (\_ -> g) s
--     compose = (.)
--     update g f s = f (g s)

-- | Reference to to an @a@ inside an @s@ structure.
--
-- This datatype is useful as a default reference.  The typeclass is provided
-- for as-yet-unconceived reference types.
data FRef s a = FRef 
    { get :: s -> a
    , set :: a -> s -> s }

composeFRef :: FRef s a -> FRef t s -> FRef t a
composeFRef sa ts = FRef { get = get sa . get ts
                         , set = updateFRef ts . set sa }

updateFRef :: FRef s a -> (a -> a) -> s -> s
updateFRef rsa f s = set rsa (f (get rsa s)) s

instance Ref FRef where
    ref = FRef
    compose = composeFRef
    update = updateFRef


------------------------------------------------------------------------------
-- References

-- | Reference to the first element of a tuple.
fst :: Ref r => r (x, y) x
fst = ref Prelude.fst (\x (_, y) -> (x, y))

-- | Reference to the second element of a tuple.
snd :: Ref r => r (x, y) y
snd = ref Prelude.snd (\y (x, _) -> (x, y))


-- data Person = P { name :: Name } deriving Show
-- data Name = N { first :: String, last :: String } deriving Show

-- p = P (N "a" "b")
-- p1 = p{ name = (name p){ last = (last . name $ p) ++ "fhqwgads" } }

-- personLastNameRef :: (Ref r) => r Person String
-- personLastNameRef = lastNameRef `compose` nameRef
--    where nameRef = ref name (\newName p -> p{ name = newName })
--          lastNameRef = ref last (\newLast n -> n{ last = newLast })
-- p1' = update (personLastNameRef :: FRef Person String) (++ "fhqwgads") p
-- ln = get personLastNameRef p1'