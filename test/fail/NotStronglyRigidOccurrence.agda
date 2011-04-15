-- Andreas, 2011-04-15
module NotStronglyRigidOccurrence where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

-- Jason C. Read, PhD thesis, p. 109
test : (k : Nat) -> 
       let X : (Nat -> Nat) -> Nat
           X = _ 
       in (f : Nat -> Nat) -> X f ≡ suc (f (X (\ x -> k)))
test k f = refl -- {a = suc (f (suc k))}
-- leads to _30 : _22 k f ≡ suc (f (_22 k (λ x → k)))
-- this should give yellow, because above solution for _22 exists
