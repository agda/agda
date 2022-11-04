-- An example from the changelog.

open import Agda.Builtin.Equality

data Unit : Set where
  unit : Unit

mutual

  f : Unit → Unit
  f = _

  @0 f≡ : f ≡ λ { unit → unit }
  f≡ = refl
