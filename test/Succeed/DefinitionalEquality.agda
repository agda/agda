
module DefinitionalEquality where

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

subst : {A : Set}(P : A -> Set){x y : A} -> x == y -> P y -> P x
subst {A} P refl p = p

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

-- This formulation of the associativity law guarantees that for closed n, but
-- possibly open m and p the law holds definitionally.

assoc : (n : Nat) -> (\m p -> n + (m + p)) == (\m p -> (n + m) + p)
assoc zero    = refl
assoc (suc n) = subst (\ ∙ -> f ∙ == f (\m p -> ((n + m) + p)))
                      (assoc n) refl
  where
    f = \(g : Nat -> Nat -> Nat)(m p : Nat) -> suc (g m p)
