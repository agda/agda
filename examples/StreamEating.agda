
module StreamEating where

-- Infinite streams

codata Stream (A : Set) : Set where
  _::_ : A -> Stream A -> Stream A

-- A stream processor SP A B consumes elements of A and produces elements of B.
-- It can only consume a finite number of A's before producing a B.

mutual
  data SP (A B : Set) : Set where
    get : (A -> SP A B) -> SP A B
    <_> : SP' A B -> SP A B

  codata SP' (A B : Set) : Set where
    put : B -> SP A B -> SP' A B

eat : {A B : Set} -> SP A B -> Stream A -> Stream B
eat (get f)      (a :: as) ~ eat (f a) as
eat < put b sp > as        ~ b :: eat sp as

_∘_ : forall {A B C} -> SP B C -> SP A B -> SP A C
get f₁        ∘ < put x sp₂ > ~ f₁ x ∘ sp₂
< put x sp₁ > ∘ sp₂           ~ < put x (sp₁ ∘ sp₂) >
sp₁           ∘ get f₂        ~ get (\x -> sp₁ ∘ f₂ x)
