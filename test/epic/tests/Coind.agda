{-# OPTIONS --universe-polymorphism #-}
module tests.Coind where

open import Prelude.IO
open import Prelude.Level
open import Prelude.Nat
open import Prelude.Unit

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

data Stream (A : Set) : Set where
  _::_ : (x : A) (xs : ∞ (Stream A)) → Stream A

ones : Stream Nat
ones = 1 :: (♯ ones)

twos : Stream Nat
twos = 2 :: (♯ twos)

incr : Nat -> Stream Nat
incr n = n :: (♯ (incr (n + 1)))

printStream : Nat -> Stream Nat -> IO Unit
printStream Z _ = putStrLn ""
printStream (S steps) (n :: ns) =
    printNat n ,,
    printStream steps (♭ ns)
    
main : IO Unit
main = 
    printStream 10 twos ,,
    printStream 10 ones ,,
    printStream 10 (incr Z)
