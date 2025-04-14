{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Agda.Builtin.Maybe

open import Auto.Prelude

-- using a type argument as a proof

h0 : (A : Set) (x₁ x₂ : ⊥) → ⊥  -- x₁ ≡ x₂
h0 = {!!}
-- Andreas, 2025-04-14, issue #7587
-- Removed the broken heuristics for absurd lambda.
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

-- Andreas, 2025-03-31, issue #7662: ♭ needs to be printed prefix rather than postfix
issue7662 : ∞ Bool → Bool
issue7662 x = {!!}

issue7587 : (A : Set) → ⊥ → ⊥
issue7587 = ?
