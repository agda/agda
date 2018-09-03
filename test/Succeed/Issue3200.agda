-- Andreas, 2018-09-03, issue #3200 reported by gallais
--
-- Record let pattern bindings trigger spurious irrelevance
-- marker, probably due to confusion of Prop with dummy type.

-- {-# OPTIONS -v tc.term.let.pattern:100 #-}
-- {-# OPTIONS -v tc.lhs.top:30 #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Unit

record R : Set where
  field
    fld : Bool

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

solve2 : Maybe (Bool → Bool)
solve2 =
  let record { fld = bla } = record { fld = true } in
  case true of λ where
    true → just (λ x → true)
    false → nothing

From-just : {A : Set} → Maybe A → Set
From-just {A} (just _) = A
From-just nothing  = ⊤

from-just : {A : Set} (x : Maybe A) → From-just x
from-just (just x) = x
from-just nothing  = _

test : Bool
test = from-just solve2 true

-- Error was:
--
-- From-just .((just (λ x → true))) should be a function type, but it isn't
-- when checking that true is a valid argument to a function of type
-- From-just solve2
