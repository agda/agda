-- Andreas, 2020-05-19, issue #4157, reported by nad

-- In old-style mutual blocks, it should be possible to have
-- several anonymous definitions.

open import Agda.Builtin.Equality

mutual

  _ : Set₁
  _ = Set

  _ : Set → Set
  _ = λ A → A

mutual

  F : Set → Set
  F = _

  _ : F ≡ λ A → A
  _ = refl

  G : Set → Set
  G = _

  _ : G ≡ λ A → A → A
  _ = refl

-- Should pass
