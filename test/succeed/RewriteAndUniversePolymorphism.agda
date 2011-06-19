{-# OPTIONS --universe-polymorphism #-}

-- The builtin equality will be the polymorphic equality
-- instantiated to Set. Rewrite should work for that.
-- Of course, it would be nice to have rewrite for the
-- polymorphic equality directly, but that requires further
-- work.

module RewriteAndUniversePolymorphism where

postulate
  Level : Set
  lzero : Level
  lsuc  : (i : Level) → Level
  _⊔_   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

infixl 6 _⊔_

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
