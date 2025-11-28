{-# OPTIONS --rewriting --experimental-irrelevance #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ

variable
  x y z : ℕ

data Vec : ..ℕ → Set where
  []   : Vec ze
  _,-_ : ℕ → Vec x → Vec (su x)

variable
  xs ys zs : Vec x

_+_ : ℕ → ℕ → ℕ
ze   + y = y
su x + y = su (x + y)

_++_ : ∀ .{x y} → Vec x → Vec y → Vec (x + y)
[]        ++ ys        = ys
(x ,- xs) ++ []        = x ,- (xs ++ [])
(x ,- xs) ++ (y ,- ys) = x ,- (xs ++ (y ,- ys))

postulate
  +-assoc : (x + y) + z ≡ x + (y + z)

{-# REWRITE +-assoc #-}

postulate
  ++-assoc : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

{-# REWRITE ++-assoc #-}

test : ∀ {xs : Vec ze} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
test = refl
