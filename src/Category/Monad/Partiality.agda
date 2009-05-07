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
  later x >>= f = later (♯ ♭ x >>= f)

-- run x for n steps peels off at most n "later" constructors from x.

run_for_steps : ∀ {A} → A ⊥ → ℕ → A ⊥
run now   x for n     steps = now x
run later x for zero  steps = later x
run later x for suc n steps = run ♭ x for n steps

-- Is the computation done?

isNow : ∀ {A} → A ⊥ → Bool
isNow (now x)   = true
isNow (later x) = false

------------------------------------------------------------------------
-- Productivity checker workaround

-- The monad can be awkward to use, due to the limitations of guarded
-- coinduction. The following code provides a (limited) workaround.

infixl 1 _>>=_

data _⊥-prog : Set → Set₁ where
  now   : ∀ {A} (x : A) → A ⊥-prog
  later : ∀ {A} (x : ∞₁ (A ⊥-prog)) → A ⊥-prog
  _>>=_ : ∀ {A B} (x : A ⊥-prog) (f : A → B ⊥-prog) → B ⊥-prog

data _⊥-whnf : Set → Set₁ where
  now   : ∀ {A} (x : A) → A ⊥-whnf
  later : ∀ {A} (x : A ⊥-prog) → A ⊥-whnf

whnf : ∀ {A} → A ⊥-prog → A ⊥-whnf
whnf (now   x) = now x
whnf (later x) = later (♭₁ x)
whnf (x >>= f) with whnf x
whnf (x >>= f) | now   x′ = whnf (f x′)
whnf (x >>= f) | later x′ = later (x′ >>= f)

mutual

  value : ∀ {A} → A ⊥-whnf → A ⊥
  value (now   x) = now x
  value (later x) = later (♯ run x)

  run : ∀ {A} → A ⊥-prog → A ⊥
  run x = value (whnf x)

------------------------------------------------------------------------
-- Examples

module Examples where

  open import Relation.Nullary

  -- McCarthy's f91:

  f91′ : ℕ → ℕ ⊥-prog
  f91′ n with n ≤? 100
  ... | yes _ = later (♯₁ (f91′ (11 + n) >>= f91′))
  ... | no  _ = now (n ∸ 10)

  f91 : ℕ → ℕ ⊥
  f91 n = run (f91′ n)
