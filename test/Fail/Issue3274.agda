
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Vec (A : Set) : Nat → Set where

variable
  A  : Set
  x  : A
  n  : Nat
  xs : Vec A n

postulate
  IsHead : A → Vec A (suc n) → Set

-- Should also work if there is pruning
solve_==_by_ : (m n : Nat) → m ≡ n → Set
solve_==_by_ _ _ _ = Nat

mutual-block : Set

meta : Nat
meta = _

-- `n` gets pruned due to the meta == suc n constraint, so we can't generalize over it
module _ (X : Set) where
  tricky : let n = _
               _ = solve meta == suc n by refl
           in IsHead {n = n} x xs → Nat
  tricky h = 0

mutual-block = Nat
