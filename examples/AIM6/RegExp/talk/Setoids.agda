module Setoids where

open import Eq
open import Prelude

record Setoid : Set1 where
  field
    carrier : Set
    _≈_     : carrier -> carrier -> Set
    equiv   : Equiv _≈_

record Datoid : Set1 where
  field
    setoid : Setoid
    _≟_    : forall x y -> Dec (Setoid._≈_ setoid x y)

Setoid-≡ : Set -> Setoid
Setoid-≡ a = record { carrier = a; _≈_ = _≡_; equiv = Equiv-≡ }
