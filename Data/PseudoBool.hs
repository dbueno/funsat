
-- | This module is intended for adding the ability to translate (general?)
-- pseudo-boolean constraints for Funsat.
--
--  * There are polynomial-size BDDs for cardinality constraints, that is,
--  constraints of the form /x1 + ... + xn >= k/.  That should probably be the
--  starting point.
module Data.PseudoBool where

-- for a package:

-- default objective: minimise number of packages selected:
--   sum ps    


data Constraint = 