
module _ where

open import Agda.Builtin.List
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

infix -1 _,_
record _×_ {a} (A B : Set a) : Set a where
  constructor _,_
  field fst : A
        snd : B
open _×_

data Constraint : Set₁ where
  mkConstraint : {A : Set} (x y : A) → x ≡ y → Constraint

infix 0 _==_
pattern _==_ x y = mkConstraint x y refl

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

deepId : {A : Set} → List A → List A
deepId []       = []
deepId (x ∷ xs) = x ∷ deepId xs

nil : Constraint
nil = _ ++ [] == 1 ∷ 2 ∷ []

neutral : List Nat → Constraint
neutral ys = _ ++ deepId ys == 1 ∷ 2 ∷ deepId ys

spine : (ys zs : List Nat) → Constraint
spine ys zs = _ ++ zs == 1 ∷ ys ++ zs

N-ary : Nat → Set → Set
N-ary zero    A = A
N-ary (suc n) A = A → N-ary n A

foo : N-ary _ Nat
foo = λ x y z → x

plus : Nat → Constraint
plus n = _ + n == 2 + n

plus-lit : Constraint
plus-lit = _ + 0 == 3

dont-fail : Nat → Nat → Constraint × Constraint
dont-fail n m =
  let X = _ in
  X + (m + 0) == n + (m + 0) , X == n
