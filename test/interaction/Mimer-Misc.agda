
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Auto.Prelude

-- using a type argument as a proof

h0 : (x₁ x₂ : ⊥) → x₁ ≡ x₂
h0 = {!!}
--h0 = λ ()

-- using dependent pair to define non-dep pair

module DND where
 _×_ : Set → Set → Set
 A × B = Σ A (λ _ → B)

 h1-2 : ∀ {A B} → A × B → B × A
 h1-2 = {!!}
-- h1-2 = λ z → Σ-i (Σ.prf z) (Σ.wit z)


-- Andreas, 2024-07-13
-- Mimer solves Agsy issue #2853

module Issue2853 where

  -- WORKS with f defined outside of the record
  -- postulate
  --   f : ∀{A : Set} → A → A

  postulate
    irr : (A : Set) (f : A → A) (a b : A) → f a ≡ f b

  -- Agsy does not deal with field f well:

  module Method where

    record R (A : Set) : Set where
      field
        f : A → A

      test : (a b : A) → f a ≡ f b
      test a b rewrite irr A f a b = {!!}  -- refl (Agsy failed, Mimer succeeds)

  -- It fails also in this situation:

  record R (A : Set) : Set where
    field
      f : A → A

  module M (A : Set) (r : R A) where
    open R r

    test : (a b : A) → f a ≡ f b
    test a b rewrite irr A f a b = {!!}  -- refl (Agsy failed, Mimer succeeds)

  -- And even here:

  postulate
     A : Set
     r : R A

  open R r

  test : (a b : A) → f a ≡ f b
  test a b rewrite irr A f a b = {!!}  -- refl (Agsy failed, Mimer succeeds)

skip-solutions : Maybe Bool
skip-solutions = {!-s 1!}
