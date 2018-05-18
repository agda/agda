
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module M (n : Nat) (m : Nat) where

  foo : n ≡ 0 → Nat
  foo refl = 0
    module M' where
      bar : Nat
      bar = m

  bad : Nat
  bad = M'.bar -- internal error Monad.Signature:882
