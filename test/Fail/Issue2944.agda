
module _ where

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool

infix -1 _,_
record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field fst : A
        snd : B
open _×_

data Constraint : Set₁ where
  mkConstraint : {A : Set} (x y : A) → x ≡ y → Constraint

infix 0 _==_
pattern _==_ x y = mkConstraint x y refl

T : Bool → Set
T false = Nat
T true  = Nat → Nat

bla : (Nat → Nat) → Nat → Nat
bla f zero = zero
bla f = f  -- underapplied clause!

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- 0 and 1 are both solutions, so should not be solved.
bad! : Constraint
bad! = bla pred _ == zero

-- Should not fail, since 2 is a solution!
more-bad! : Constraint
more-bad! = bla pred _ == 1

-- Same thing for projections

blabla : Nat → Nat × Nat
blabla zero    = 1 , 1
blabla (suc n) = 0 , n

-- Don't fail: 0 is a valid solution
oops : Constraint
oops = fst (blabla _) == 1

bla₂ : Bool → Nat × Nat
bla₂ false = 0 , 1
bla₂ true .fst = 0
bla₂ true .snd = 1

-- Don't solve: false and true are both solutions
wrong : Constraint
wrong = bla₂ _ .fst == 0
