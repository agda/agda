{-# OPTIONS --guardedness #-}

module Issue826-2 where

open import Common.Coinduction

data _≡_ {A : Set} (x y : A) : Set where

data D : Set where
  c : ∞ D → D

delay : D → ∞ D
delay x = ♯ x

data P : D → Set where
  o : (x : ∞ D) → P (♭ x) → P (c x)

postulate
  h : (x : D) → P x → P x

f : (x : D) → P (c (delay x)) → P x
f x (o .(delay x) p) = h x p

g : (x : D) → P x → P (c (delay x))
g x p = h (c (delay x)) (o (delay x) p)

postulate
  bar : (x : ∞ D) (p : P (♭ x)) →
        h (c x) (o x (h (♭ x) p)) ≡ o x p

foo : (x : D) (p : P (c (delay x))) → g x (f x p) ≡ p
foo x (o .(delay x) p) = goal
  where
  x′ = _

  goal : _ ≡ o x′ p
  goal = bar x′ p

-- The following error message seems to indicate that an expression is
-- not forced properly:
--
--   Bug.agda:30,26-30
--   ♭ (.Bug.♯-0 x) != x of type D
--   when checking that the expression goal has type
--   g x (f x (o (.Bug.♯-0 x) p)) ≡ o (.Bug.♯-0 x) p
--
-- Thus it seems as if this problem affects plain type-checking as
-- well.
