-- Andreas, 2019-11-12, issue #4168b
--
-- Meta variable solver should not use uncurrying
-- if the record type contains erased fields.

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Common.IO

P : (A B : Set) → (A → B) → Set
P A B f = (y : B) → Σ A (λ x → f x ≡ y)

record R (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x

p : (A B : Set) (r : R A B) → P A B (R.to r)
p _ _ r y = R.from r y , to-from y
  where
  postulate
    to-from : ∀ x → R.to r (R.from r x) ≡ x

record Box (A : Set) : Set where
  constructor box
  field
    @0 unbox : A

test : (A : Set) → P (Box A) (Box (Box A)) (box {A = Box A})
test A = p _ _ (record
  { to      = box {A = _}
  ; from    = λ { (box (box x)) → box {A = A} x }
      -- at first, a postponed type checking problem ?from
  ; from-to = λ x → refl {A = Box A} {x = _}
  })
-- from-to creates constraint
--
--   x : Box A |- ?from (box x) = x : Box A
--
-- This was changed to
--
--   y : Box (Box A) |- ?from y = unbox y : Box A
--
-- which is an invalid transformation since x is not
-- guaranteed to be in erased context.

-- As a consequence, compilation (GHC backend) failed.


-- A variant with a non-erased field.

record ⊤ : Set where

record Box' (A : Set) : Set where
  constructor box'
  field
    unit : ⊤
    @0 unbox' : A

test' : (A : Set) → P (Box' A) (Box' (Box' A)) (box' {A = Box' A} _)
test' A = p _ _ (record
  { to      = box' {A = _} _
  ; from    = λ { (box' _ (box' _ x)) → box' {A = A} _ x }
  ; from-to = λ x → refl {A = Box' A} {x = _}
  })

-- UPDATE (2019-11-17):
-- We may, however, uncurry if the record argument is erased.

mutual
  X : {@0 A : Set} (@0 b : Box A) → Box (Box A)
  X = _

  spec : ∀{@0 A : Set} {@0 x : A}
       → X (box x) ≡ box (box x)
  spec = refl

  --  This can be solved by:
  --  X := λ {@0 A} (@0 b) → box (box (Box.unbox b))


main : IO ⊤
main = return _
