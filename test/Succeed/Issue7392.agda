open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

it : {{Nat}} → Nat
it {{x}} = x

fails : {{x : Nat}} (y : Nat) → x ≡ suc y → Nat
fails y refl = it

failstoo : {{x : Nat}} (y : Nat) → x ≡ y → Nat
failstoo {{x}} y refl = it

failstree : (x : Nat) {{y : Nat}} → x ≡ y → Nat
failstree x {{y}} refl = it
