-- Jesper, 2017-08-13: This test case now fails since instantiation
-- of metavariables during case splitting was disabled (see #2621).

{-# OPTIONS -v tc.conv.irr:50 #-}
-- {-# OPTIONS -v tc.lhs.unify:50 #-}
module IndexInference where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 40 _::_

-- The length of the vector can be inferred from the pattern.
foo : Vec Nat _ -> Nat
foo (a :: b :: c :: []) = c

-- Andreas, 2012-09-13 an example with irrelevant components in index

pred : Nat → Nat
pred (zero ) = zero
pred (suc n) = n

data ⊥ : Set where
record ⊤ : Set where

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc n) = ⊤

data Fin (n : Nat) : Set where
  zero : .(NonZero n) → Fin n
  suc  : .(NonZero n) → Fin (pred n) → Fin n

data SubVec (A : Set)(n : Nat) : Fin n → Set where
  []   : .{p : NonZero n} → SubVec A n (zero p)
  _::_ : .{p : NonZero n}{k : Fin (pred n)} → A → SubVec A (pred n) k → SubVec A n (suc p k)

-- The length of the vector can be inferred from the pattern.
bar : {A : Set} → SubVec A (suc (suc (suc zero))) _ → A
bar (a :: []) = a
