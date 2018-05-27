-- Andreas, 2016-10-23 issue #2280:
-- Solver throws away meta arguments.
-- (Issue discovered by code review.)

open import Common.Equality
open import Common.Product

data Bool : Set where
  true false : Bool

postulate
  not : Bool → Bool

data D (f : Bool → Bool) : Set where
  c : ∀ x → x ≡ not (f true) → D f

test : D {!!}
test = c {!!} refl

-- C-c C-= says
-- ?1 := not (?0 true)

-- But C-c C-s solves
-- ?1 := not ?

-- Ulf says this is fine, since we create a new interaction meta.
-- I must agree.

data E (p : Bool × Bool) : Set where
  c : ∀ x → x ≡ not (proj₁ p) → E p

test2 : E {!!}
test2 = c {!!} refl

-- Consequently, C-c C-s should solve the last meta as
-- ?3 := not ?
