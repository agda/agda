-- A memoised implementation of the Fibonacci sequence, following
-- Hinze's "Memo functions, polytypically!".

module Issue2918 where

open import Agda.Builtin.IO
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Size
open import Agda.Builtin.Unit

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

mutual

  data Nat (i : Size) : Set where
    zero : Nat i
    suc  : Nat′ i → Nat i

  data Nat′ (i : Size) : Set where
    [_] : {j : Size< i} → Nat j → Nat′ i

mutual

  ℕ→Nat : ℕ → Nat ∞
  ℕ→Nat zero    = zero
  ℕ→Nat (suc n) = suc (ℕ→Nat′ n)

  ℕ→Nat′ : ℕ → Nat′ ∞
  ℕ→Nat′ n = [ ℕ→Nat n ]

mutual

  Nat′[_]→ : Size → Set → Set
  Nat′[ i ]→ A = A × Nat′[ i ]→′ A

  record Nat′[_]→′ (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Nat′[ j ]→ A

open Nat′[_]→′ public

tabulate : ∀ {i} {A : Set} → (Nat′ i → A) → Nat′[ i ]→′ A
force (tabulate f) = f [ zero ] , tabulate (λ n → f [ suc n ])

lookup : ∀ {i} {A : Set} → Nat′[ i ]→′ A → Nat′ i → A
lookup t [ zero  ] = proj₁ (force t)
lookup t [ suc n ] = lookup (proj₂ (force t)) n

memo-fix :
  {A : Set} →
  (∀ {i} → (Nat′ i → A) → (Nat i → A)) →
  ∀ {i} → Nat′ i → A
memo-fix f =
  wrapper λ { [ n ] → f (lookup (tabulate (memo-fix f))) n }
  where
  wrapper : ∀ {i} {A : Set} → (Nat′ i → A) → (Nat′ i → A)
  wrapper f [ n ] = f [ n ]

fib-step : ∀ {i} → (Nat′ i → ℕ) → (Nat i → ℕ)
fib-step fib zero            = 0
fib-step fib (suc [ zero ])  = 1
fib-step fib (suc [ suc n ]) = fib n + fib [ suc n ]

fib : ℕ → ℕ
fib n = memo-fix fib-step [ ℕ→Nat n ]

postulate
  crash-after-ten-seconds : ℕ → IO ⊤

{-# FOREIGN GHC
  import qualified Control.Exception
  import qualified System.Timeout

  crashAfterTenSeconds c = do
    r <- System.Timeout.timeout (10 * 10^6)
                                (Control.Exception.evaluate c)
    case r of
      Nothing -> error "The computation timed out"
      Just _  -> return ()
  #-}

{-# COMPILE GHC crash-after-ten-seconds = crashAfterTenSeconds #-}

main : IO ⊤
main = crash-after-ten-seconds (fib 300)
