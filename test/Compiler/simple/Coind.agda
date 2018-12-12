{-# OPTIONS --guardedness #-}
module Coind where

open import Common.IO
open import Common.Level
open import Common.Nat
open import Common.Unit
open import Common.Coinduction renaming (♯_ to sharp; ♭ to flat)

{-
infix 1000 sharp_

postulate
  Infinity  : ∀ {a} (A : Set a) → Set a
  sharp_ : ∀ {a} {A : Set a} → A → Infinity A
  flat  : ∀ {a} {A : Set a} → Infinity A → A

{-# BUILTIN INFINITY Infinity  #-}
{-# BUILTIN SHARP    sharp_ #-}
{-# BUILTIN FLAT     flat  #-}
-}

data Stream (A : Set) : Set where
  _::_ : (x : A) (xs : ∞ (Stream A)) → Stream A

ones : Stream Nat
ones = 1 :: (sharp ones)

twos : Stream Nat
twos = 2 :: (sharp twos)

incr : Nat -> Stream Nat
incr n = n :: (sharp (incr (n + 1)))

printStream : Nat -> Stream Nat -> IO Unit
printStream zero _ = putStrLn ""
printStream (suc steps) (n :: ns) =
    printNat n ,,
    printStream steps (flat ns)

main : IO Unit
main =
    printStream 10 twos ,,
    printStream 10 ones ,,
    printStream 10 (incr zero)
