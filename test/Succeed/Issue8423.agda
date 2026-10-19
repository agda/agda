open import Agda.Builtin.Equality
open import Agda.Primitive

data D (a : Level) : Set a where
  c : D a

F :
  (A : Set) (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ : A) →
  _≡_ {A = D lzero} c c
F A x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = g x
  where
  f : A → D _
  f _ = c

  g : ∀ x → f x ≡ f x
  g x with x
  … | _ = refl
