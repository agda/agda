module MissingDefinition where

open import Agda.Builtin.Equality

Q : Set

U : Set
T : U → Set
T _ = U

V : Set
W : V → Set

private

  X : Set

module AB where

  A : Set
  B : (a b : A) → a ≡ b

mutual

  U₂ : Set
  T₂ : U₂ → Set
