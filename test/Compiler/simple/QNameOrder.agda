
module _ where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Common.Prelude

_<_ = primQNameLess

True : Bool → Set
True true  = ⊤
True false = ⊥

zzz aaa : ⊤
zzz = _
aaa = _

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

check : (x y : Name) → True (x < y) → String
check x y prf with x < y
check x y prf | true = "A-ok"
check x y prf | false = ⊥-elim prf

main : IO Unit
main = putStrLn (check (quote zzz) (quote aaa) _)
