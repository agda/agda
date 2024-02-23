module InstanceDiscrimEta where

open import Agda.Builtin.Unit

postulate
  X : ⊤ → Set
  t : ⊤

  it : ⦃ _ : X tt ⦄ → Set

  instance _ : X t

_ : Set
_ = it
