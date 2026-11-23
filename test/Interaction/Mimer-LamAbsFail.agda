-- Mimer used to crash with a type error here instead of reporting
-- that it found no solution: lambda-abstracting the function argument
-- of cong woke up a postponed constraint, which failed.
-- Now it finds  cong suc e  (after the lambda body got pruned).

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

test1 : (n : Nat) → n ≡ 0 → suc n ≡ 1
test1 n e = {!cong!}

