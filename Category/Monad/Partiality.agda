------------------------------------------------------------------------
-- The partiality monad
------------------------------------------------------------------------

module Category.Monad.Partiality where

open import Coinduction
open import Category.Monad
open import Data.Nat
open import Data.Bool

-- The partiality monad.

data _⊥ (A : Set) : Set where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥

monad : RawMonad _⊥
monad = record
  { return = now
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : ∀ {A B} → A ⊥ → (A → B ⊥) → B ⊥
  now x   >>= f = f x
  later x >>= f = later >>=′
    where >>=′ ~ ♯ ♭ x >>= f

-- run x for n steps peels off at most n "later" constructors from x.

run_for_steps : ∀ {A} → A ⊥ → ℕ → A ⊥
run now   x for n     steps = now x
run later x for zero  steps = later x
run later x for suc n steps = run ♭ x for n steps

-- Is the computation done?

isNow : ∀ {A} → A ⊥ → Bool
isNow (now x)   = true
isNow (later x) = false
