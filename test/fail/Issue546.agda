module Issue546 where

data I : Set where
  i : I

data ⊤ : Set where
  tt : ⊤

abstract
  P : I → Set
  P i = ⊤

Q : P i → Set
Q _ = ⊤

q : Q tt
q = tt

-- Q tt should be rejected.

-- This bug was introduced in Agda 2.3.0.