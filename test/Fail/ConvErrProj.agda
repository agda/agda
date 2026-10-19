module ConvErrProj where

open import Agda.Builtin.Equality

record Field : Set₁ where
  field
    carrier : Set
    _+_ _*_ : carrier → carrier → carrier

module _ (𝔽 : Field) where
  open Field 𝔽
  test : ∀ x y → x + y ≡ x * y
  test x y = refl

-- error should say x + y != x * y
-- not Field._+_ != Field._*_
