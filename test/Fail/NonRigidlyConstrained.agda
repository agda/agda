
module _ where

data Nat : Set where

postulate
  C Q : Set → Set
  unQ : ∀ {A} → Q A → A
  instance
    CQ : C (Q Nat)

  theC : {A : Set} {{_ : C A}} → A

-- We shouldn't solve this based on CQ being the only instance available for Q _.
dont-solve : _
dont-solve = unQ theC
