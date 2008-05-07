module SnarfRecords where

import Text.Regex
import Test.QuickCheck( quickCheck )

-- | Assume the input contains @n>0@ records delimited at the start by
-- whatever matches regexp.  Each element @s@ of @groups rx f s@ is the output
-- of @f@ when passed (1) a string that starts with a matche for @rx@ and (2)
-- the rest of the string up to (and not including) the next match of @rx@.
--
-- If the regex fails to match at all (i.e. @n=0@), the empty list is
-- returned.
groups :: Regex -> String -> [(String, String)]
groups markerRx s = snd $ groups' markerRx s
  where
    -- Returns the text before the match, if any match, in its first position.
    groups' markerRx s =
        case matchRegexAll markerRx s of
          Nothing -> (s, [])
          Just (beforeMatch, matched, afterMatch, _submatches) ->
              let (beforeNext, retList) = groups' markerRx afterMatch
              in ( beforeMatch, (matched, beforeNext) : retList )

-- The grouping should just be a partition of the input string, or empty if
-- there is no match.
prop_groups_partition rx s =
    case matchRegex rx s of
      Nothing -> True
      Just _  -> s == (concat . map (uncurry (++))) (groups rx s)

-- Each group should begin with a match.
prop_groups_matches rx s =
    all rxMatchesStart (map (uncurry (++)) $ groups rx s)
  where rxMatchesStart sub =
            case matchRegexAll rx sub of
              Nothing -> False
              Just (beforeMatch, matched, afterMatch, _) ->
                  beforeMatch == ""
                  && sub == matched ++ afterMatch
       






---- Main

main = undefined