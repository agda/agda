module Issue1441 where

open import Common.Nat
open import Common.Unit
open import Common.IO


data Sing : (n : Nat) → Set where
  sing : ∀ n → Sing n

data D : Set → Set where
  c : ∀ n → D (Sing n)

test : (A : Set) → D A → Nat
test .(Sing n) (c n) = n

main : IO Unit
main = printNat (test (Sing 1) (c 1))

-- should succeed and print 1
