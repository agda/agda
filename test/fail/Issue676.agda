
module Issue676 where

data Bool : Set where
  true false : Bool

data ⊥ : Set where

data Silly A : Set where
  [_]  : A → Silly A
  fail : ⊥ → Silly A

-- This shouldn't be projection-like since the second clause won't reduce.
unsillify : ∀ {A} → Silly A → A
unsillify [ x ] = x
unsillify (fail ())

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

-- Triggers an __IMPOSSIBLE__ if unsillify is projection like.
bad : (x : ⊥) → unsillify (fail x) ≡ true
bad x = refl
