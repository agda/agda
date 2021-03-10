data Bool : Set where
  true false : Bool

postulate
  and : Bool → Bool → Bool

-- WAS: splitting on y removes the x@ as-pattern
test : Bool → Bool → Bool
test x@true y  = {!y!}
test x@false y = and x {!y!}  -- x will go out of scope if we split on y

-- Multiple as-patterns on the same pattern should be preserved in the
-- right order.
test₂ : Bool → Bool → Bool
test₂ x@y@true z = {!z!}
test₂ x@y z = {!!}

open import Agda.Builtin.String

-- As bindings on literals should also be preserved
test₃ : String → Bool → Bool
test₃ x@"foo" z = {!z!}
test₃ _ _ = {!!}
