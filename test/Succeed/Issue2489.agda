
module _ where

module First where
  postulate
    C  : Set → Set
    it : {A : Set} ⦃ _ : C A ⦄ → A
    X  : Set

module Second where
  open First
  postulate instance iCX : C X

module Nested where
  open First
  x : X
  x = it   -- Second.iCX is in scope
