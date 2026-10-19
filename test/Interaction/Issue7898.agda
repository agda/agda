open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  Foo : (n m : Nat) → n + m ≡ 3 → Set

_ = Foo {!!} {!!} refl
