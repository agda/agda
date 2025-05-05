module Issue7856 where

open import Agda.Builtin.Unit

apply : (Set → Set) → Set → Set
apply f = f

-- Reported by Javier Díaz, reproducer by Szumi Xie: extended lambdas
-- defined in type signatures should not belong to opaque blocks.

opaque
  test : apply (λ {x → x}) ⊤
  test = tt

_ : ⊤
_ = test
