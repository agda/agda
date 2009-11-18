{-# OPTIONS --universe-polymorphism #-}

-- The builtin equality will be the polymorphic equality
-- instantiated to Set. Rewrite should work for that.
-- Of course, it would be nice to have rewrite for the
-- polymorphic equality directly, but that requires further
-- work.

module RewriteAndUniversePolymorphism where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

infixl 6 _⊔_

_⊔_ : Level -> Level -> Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infix 4 _≡_

data _≡_ {a}{A : Set a} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

test : (a b : ℕ) → a ≡ b → b ≡ a
test a b eq rewrite eq = refl
