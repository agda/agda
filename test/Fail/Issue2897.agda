
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data ⊥ : Set where

T : Nat → Set
T zero    = ⊥
T (suc n) = Nat

module M (n : Nat) where

  foo : n ≡ 0 → T n → Nat
  foo refl t = 0
    module M' where
      bar : ⊥
      bar = t

  bad : ⊥
  bad = M'.bar

loop : ⊥
loop = M.bad 0
