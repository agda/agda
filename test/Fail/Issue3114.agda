open import Agda.Builtin.Equality

postulate
  A : Set
  a : A
  b : A

mutual
  Meta : A → A → A → A
  Meta = ?

  _ : Meta a ≡ Meta b
  _ = refl
