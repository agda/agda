open import Common.Prelude
open import Common.Equality

test : "foo" ≡ "bar" → Set₁
test refl = Set
