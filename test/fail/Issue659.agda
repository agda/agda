-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta:50 -v tc.conv:20 -v tc.conv.type:50 #-}
module Issue659 where

postulate
  Level : Set
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

record R (ℓ : Level) : Set ℓ where

postulate
  r : ∀ ℓ → R ℓ

module M (r : ∀ ℓ → R ℓ) where

  data D (ℓ : Level) : Set ℓ where

  id : ∀ {a} {A : Set a} → A → A
  id x = x

  data K : Set where
    k₁ k₂ : K

  P : ∀ {ℓ} → K → Set ℓ → Set ℓ
  P k₁ A = A → A
  P k₂ A = D _

open M r

postulate
  Foo : ∀ {k a} {A : Set a} → P k A → Set

Bar : Set
Bar = Foo M.id

-- Could this error message be improved?

-- Setω is not a valid type.
-- when checking that the expression M.id has type P M.k₁ _34

-- New error:
--
-- ((r₁ : (ℓ : Level) → R ℓ) {a : Level} {A : Set a} → A → A) !=<
-- (P {_33} _32 _34)
-- because this would result in an invalid use of Setω
-- when checking that the expression M.id has type (P {_33} _32 _34)
