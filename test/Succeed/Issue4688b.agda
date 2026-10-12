open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

mutual

  A : Set
  A = _

  postulate
    B : Set
    b : B

    f : {{B}} → Set

  -- The order of these two instances should not matter
  instance
    inst₁ : {A} → B
    inst₁ = b

    inst₂ : B
    inst₂ = b

  test : Set
  test = f

  _ : A ≡ Bool
  _ = refl

