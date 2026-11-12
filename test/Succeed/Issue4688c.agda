
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat

data MyNat : Set where
  zero : MyNat
  suc  : MyNat → MyNat

postulate
  convert : {{_ : ⊤}} → Nat → MyNat

instance
  myInst : Number MyNat
  myInst .Number.Constraint = λ _ → ⊤
  myInst .Number.fromNat = λ n → convert n
