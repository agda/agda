{-# OPTIONS --erasure #-}

module Issue6413-2 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.Strict
open import Agda.Builtin.Unit

postulate
  print : Bool → IO ⊤

{-# FOREIGN GHC
      import qualified Data.Char
  #-}
{-# COMPILE GHC print = putStrLn . map Data.Char.toLower . show #-}
{-# COMPILE JS  print =
      x => cb => { process.stdout.write(x.toString() + "\n"); cb(0); }
  #-}

data ⊥ : Set where

⊥-elim : {A : Set} → @0 ⊥ → A
⊥-elim ()

f : (n : Nat) → @0 (0 ≡ 0 → ⊥) → Nat
f zero    not-zero = ⊥-elim (not-zero refl)
f (suc n) _        = n

x : @0 (0 ≡ 0 → ⊥) → Nat
x = f zero

main : IO ⊤
main = print (primForce x λ _ → true)
