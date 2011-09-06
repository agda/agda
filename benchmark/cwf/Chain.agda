
module Chain
  {U : Set}(T : U -> Set)
  (_==_ : {a b : U} -> T a -> T b -> Set)
  (refl : {a : U}(x : T a) -> x == x)
  (trans : {a b c : U}(x : T a)(y : T b)(z : T c) -> x == y -> y == z -> x == z)
  where

infix 30 _∼_
infix 3 proof_
infixl 2 _≡_by_
infix 1 _qed

data _∼_ {a b : U}(x : T a)(y : T b) : Set where
  prf : x == y -> x ∼ y

proof_ : {a : U}(x : T a) -> x ∼ x
proof x = prf (refl x)

_≡_by_ : {a b c : U}{x : T a}{y : T b} -> x ∼ y -> (z : T c) -> y == z -> x ∼ z
prf p ≡ z by q = prf (trans _ _ _ p q)

_qed : {a b : U}{x : T a}{y : T b} -> x ∼ y -> x == y
prf p qed = p
