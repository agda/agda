open import Agda.Builtin.Nat
open import Agda.Builtin.List

pattern z = zero

pattern
  one = suc zero
  two = suc one

  _◂_◂_ a b tl = a ∷ b ∷ tl

pattern

  one : Nat → Nat
  one = suc zero
  infixr 5 _◂_◂_

pattern

  _◂_◂_ : {A : Set} → A → List A → List A
  a ◂ b ◂ tl = a ∷ b ∷ tl

-- Unbound variables in pattern synonym:  a b tl
-- when scope checking the declaration
--   pattern
--     _◂_◂_ : {A : Set} → A → List A → List A
--     a ◂ b ◂ tl = a ∷ b ∷ tl
