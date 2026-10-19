module ConvErrCtxLam where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

f : ∀ (X : Set) {A : Set} {x y : A} → x ≡ y → x ≡ y
f = λ { _ refl → refl }

postulate
  X : {f : 0 ≡ 0 → 0 ≡ 0} → Set

-- tests reconstruction of enclosing *lambdas* around a conversion
-- checking error, and that i didn't mangle the scope in the process
_ : (Z : Set) -> X {f = f Z {Nat} {0} {0}} → X {f = λ x → x}
_ = λ Z y → y
