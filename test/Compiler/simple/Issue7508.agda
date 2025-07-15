
module Issue7508 where

open import Common.IO
open import Common.Unit

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

rng : Bool → Nat → Nat
rng _ _ = 4

flip : (Bool → Nat → Nat) → (Nat → Bool → Nat)
flip f a b = f b a

rng' : Nat → Bool → Nat
rng' = flip rng

main : IO Unit
main = printNat (rng' 4 true)
