------------------------------------------------------------------------
-- Equivalence relations
------------------------------------------------------------------------

module Eq where

infix 4 _≡_

------------------------------------------------------------------------
-- Definition

record Equiv {a : Set} (_≈_ : a -> a -> Set) : Set where
  field
    refl      : forall x       -> x ≈ x
    sym       : forall {x y}   -> x ≈ y -> y ≈ x
    _`trans`_ : forall {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

------------------------------------------------------------------------
-- Propositional equality

data _≡_ {a : Set} (x : a) : a -> Set where
  refl : x ≡ x

subst : forall {a x y} ->
  (P : a -> Set) -> x ≡ y -> P x -> P y
subst _ refl p = p

cong : forall {a b x y} ->
  (f : a -> b) -> x ≡ y -> f x ≡ f y
cong _ refl = refl

Equiv-≡ : forall {a} -> Equiv {a} _≡_
Equiv-≡ {a} =
  record { refl      = \_ -> refl
         ; sym       = sym
         ; _`trans`_ = _`trans`_
         }
  where
  sym : {x y : a} -> x ≡ y -> y ≡ x
  sym refl = refl

  _`trans`_ : {x y z : a} -> x ≡ y -> y ≡ z -> x ≡ z
  refl `trans` refl = refl
