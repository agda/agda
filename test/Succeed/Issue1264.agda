-- Andreas, 2014-08-30, reported by asr
-- All of the following corecursive functions from Data.Stream
-- should pass the termination checker.

{-# OPTIONS --cubical-compatible --guardedness #-}
-- {-# OPTIONS -v term:20 #-}

open import Common.Coinduction
open import Common.Prelude renaming (Nat to ℕ) hiding (_∷_; map)

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

zipWith : ∀ {A B C} →
          (A → B → C) → Stream A → Stream B → Stream C
zipWith _∙_ (x ∷ xs) (y ∷ ys) = (x ∙ y) ∷ ♯ zipWith _∙_ (♭ xs) (♭ ys)

drop : ∀ {A} → ℕ → Stream A → Stream A
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

repeat : ∀ {A} → A → Stream A
repeat x = x ∷ ♯ repeat x

iterate : ∀ {A} → (A → A) → A → Stream A
iterate f x = x ∷ ♯ iterate f (f x)

-- Interleaves the two streams.

infixr 5 _⋎_

_⋎_ : ∀ {A} → Stream A → Stream A → Stream A
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

mutual

  -- Takes every other element from the stream, starting with the
  -- first one.

  evens : ∀ {A} → Stream A → Stream A
  evens (x ∷ xs) = x ∷ ♯ odds (♭ xs)

  -- Takes every other element from the stream, starting with the
  -- second one.

  odds : ∀ {A} → Stream A → Stream A
  odds (x ∷ xs) = evens (♭ xs)
