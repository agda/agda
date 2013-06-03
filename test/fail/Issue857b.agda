-- {-# OPTIONS -v reify:100 -v syntax.reify:100  #-}
module Issue857b where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

_∋_ : (A : Set) → A → A
_ ∋ x = x

foo : {A B : Set} {x : ⊥} {y : B} →
      ((⊥ → A) ∋ λ()) x ≡ ((⊥ → B → A) ∋ λ()) x y
foo = refl

-- WAS: An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:514

bar : {A B C : Set} {x : ⊥} {y : B} {z : C} →
      ((⊥ → B → A) ∋ λ()) x y ≡ ((⊥ → C → A) ∋ λ()) x z
bar = refl

-- WAS:
-- .y != .z of type .B
-- when checking that the expression refl has type
-- ((⊥ → .B → .A) ∋ .Test.absurdLambda) .x .y ≡
-- ((⊥ → .C → .A) ∋ .Test.absurdLambda) .x .z

-- Note that z has type C, not B.

baz : {A : Set} → _≡_ {A = ⊥ → A} ⊥-elim (λ())
baz = refl

-- WAS: An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:51

-- ERROR: ⊥-elim x != (λ ()) x of type .A
-- when checking that the expression refl has type ⊥-elim ≡ (λ ())
