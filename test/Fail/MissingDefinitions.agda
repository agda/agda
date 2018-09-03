module MissingDefinitions where

open import Agda.Builtin.Equality

Q : Set

data U : Set
S : Set
S = U
T : S → Set
T _ = U

V : Set
W : V → Set

private

  X : Set

module AB where

  data A : Set
  B : (a b : A) → a ≡ b

mutual

  U₂ : Set
  data T₂ : U₂ → Set
  V₂ : (u₂ : U₂) → T₂ u₂ → Set
  data W₂ (u₂ : U₂) (t₂ : T₂ u₂) : V₂ u₂ t₂ → Set
