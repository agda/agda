
module Issue4037.Import where

open import Agda.Builtin.Equality
open import Issue4037.Dec

postulate
  Id : Set
  _≟_ : (x y : Id) → Dec (x ≡ y)
