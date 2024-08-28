open import Agda.Builtin.Equality

postulate
  A : Set

mutual
  I : (A → A) → .A → A
  I f = _

  testQ : {f : .A → A} → I f ≡ f
  testQ = refl
