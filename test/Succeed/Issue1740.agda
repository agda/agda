-- Andreas, 2015-12-12, report by Ulf, 2015-12-09

{-# OPTIONS -v tc.with.40 #-}

open import Common.Equality
open import Common.Bool

T : Bool → Set
T true  = Bool
T false = true ≡ false

foo : (a b : Bool) → a ≡ b → T a → T b
foo a b eq x rewrite eq = x

data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅ x

-- Intended new rewrite
refl-rewrite : ∀ a (eq : a ≡ a) (t : T a) → foo a a eq t ≡ t
refl-rewrite a eq t with eq
refl-rewrite a eq t | refl = refl

test : ∀ a (eq : a ≡ a) (t : T a) → foo a a eq t ≡ t
test a eq t rewrite eq = refl  -- FAILS, this is the original issue report
-- Error:
-- foo a a eq t | a | eq != t of type T a
-- when checking that the expression refl has type foo a a eq t ≡ t
-- test a refl t = refl  -- WORKS, of course

-- Non-reflexive rewrite
works : ∀ a b (eq : a ≡ b) (t : T a) → foo a b eq t ≅ t
works a b eq t rewrite eq = refl

-- Manual desugaring of old-style rewrite works as well
old-rewrite : ∀ a (eq : a ≡ a) (t : T a) → foo a a eq t ≡ t
old-rewrite a eq t with a | eq
old-rewrite a eq t | _ | refl = refl
