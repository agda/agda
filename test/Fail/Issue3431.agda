-- Jesper, 2018-12-04, Issue #3431 reported by François Thiré on the
-- Agda mailing list
-- (https://lists.chalmers.se/pipermail/agda/2018/010686.html)

-- The instance of the Reduce typeclass for pairs did not have an
-- implementation for reduceB' (only reduce'), which made it default
-- to the standard implementation and forget the blocking tags.

{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

0ℓ : Level
0ℓ = lzero

1ℓ : Level
1ℓ = lsuc lzero

-- Jesper, 2019-06-07: Rewrite rules on type constructors are no
-- longer allowed, so we have to postulate Lift instead.
postulate
  Lift : ∀ {a} ℓ (A : Set a) → Set (a ⊔ ℓ)
  lift : ∀ {a} {ℓ} {A : Set a} → A → Lift ℓ A
  lower : ∀ {a} {ℓ} {A : Set a} → Lift ℓ A → A
  lower-lift : ∀ {a} {ℓ} {A : Set a} → (x : A) → lower {ℓ = ℓ} (lift x) ≡ x
{-# REWRITE lower-lift #-}

postulate
  prod  : {ℓ ℓ′ : Level} → (A : Set ℓ) → (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)

  p : Set 1ℓ → Set 1ℓ
  q : Set 1ℓ → Set 1ℓ
  f : ∀ (c : Set 0ℓ) → p (Lift 1ℓ c) → q (Lift 1ℓ c)
  g : ∀ (a : Set 1ℓ) → ∀ (b : Set 1ℓ) → p (prod a b)
  a : Set 0ℓ
  b : Set 0ℓ

  canL : {ℓ ℓ′ ℓ″ : Level} → (A : Set ℓ) → (B : Set ℓ′)  → (prod (Lift ℓ″ A) B) ≡ Lift (ℓ″ ⊔ ℓ′) (prod A B)
  canR : {ℓ ℓ′ ℓ″ : Level} → (A : Set ℓ) → (B : Set ℓ′)  → (prod A (Lift ℓ″ B)) ≡ Lift (ℓ ⊔ ℓ″) (prod A B)
  canT : {ℓ ℓ′ ℓ″ : Level} → (A : Set ℓ) → Lift ℓ″ (Lift ℓ′ A) ≡ Lift (ℓ″ ⊔ ℓ′) A

{-# REWRITE canL #-}
{-# REWRITE canR #-}
{-# REWRITE canT #-}

ali : q (Lift 1ℓ (prod a b))
ali = f (prod a b) (g (Lift 1ℓ {!!}) (Lift 1ℓ b))

-- WAS: Set₁ != Set
-- SHOULD: succeed (with unsolved metas and constraints)
