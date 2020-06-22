open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

works : Nat → Nat
works 0 = 0
works x@(suc _) = x

forced-implicit : ∀ x {y} → x ≡ y → Nat
forced-implicit x .{x} refl = x

forced-instance : ∀ x {{y}} → x ≡ y → Nat
forced-instance x .{{x}} refl = x

fails : ∀ {x : Nat} → Nat
fails {0} = 0
fails x@{suc _} = x

forced-implicit' : ∀ x {y} → x ≡ y → Nat
forced-implicit' x x@.{_} refl = x

forced-instance' : ∀ x {{y}} → x ≡ y → Nat
forced-instance' x x@.{{_}} refl = x
