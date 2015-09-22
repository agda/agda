-- Andreas, 2012-05-04
module PruningNonMillerPatternFail where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- bad variable y is not in head position under lambda, so do not prune
fail4 : let X : Nat -> Nat -> Nat
            X = _ -- λ x y → suc x
            Y : Nat → ((Nat → Nat) → Nat) -> Nat
            Y = _  -- More than one solution:
                   -- λ x f → x
                   -- λ x f → f (λ z → x)
        in  (C : Set) ->
            (({x y : Nat} -> X x x ≡ suc (Y x (λ k → k y))) ->
             ({x y : Nat} -> Y x (λ k → k x) ≡ x)           ->
             ({x y : Nat} -> X (Y x (λ k → k y)) y ≡ X x x) -> C) -> C
fail4 C k = k refl refl refl

-- this should not solve, since there are more than one solutions for Y
