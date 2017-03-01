-- Andreas, 2017-03-01 issue #2480, reported by nad, discovered by simonhu
-- Exploit by Jesper Cockx

-- {-# OPTIONS -v tc.lhs.split:60 #-}

open import Agda.Builtin.Equality

data Bool : Set where
  tt ff : Bool

const : Bool → (Bool → Bool)
const = λ x _ → x

ap : {A : Set} {B : Set} (f : A → B) {a b : A} (p : a ≡ b) → f a ≡ f b
ap f refl = refl

mutual
  -- Type of constant boolean functions, using @UnusedArg@
  Bool→cBool : Set
  Bool→cBool = _

  accepted : (p : const tt ≡ const ff) → ap (λ f → f tt) p ≡ ap (λ f → f ff) p
  accepted p = refl {x = ap {A = Bool→cBool} (λ f → f tt) p}

constant : (f : Bool→cBool) (x y : Bool) → f x ≡ f y
constant f x y = refl

swap : Bool→cBool
swap tt = ff
swap ff = tt
-- swap is definitely not constant, should be rejected

BOOM : tt ≡ ff
BOOM = constant swap ff tt
