open import Agda.Builtin.Equality

opaque transparent

  A : Set₁
  A = Set

_ : A ≡ Set
_ = refl

opaque

  B : Set₁
  B = Set
    module B where transparent
    C : Set₁
    C = Set

_ : B.C ≡ Set
_ = refl
