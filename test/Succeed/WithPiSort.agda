-- https://github.com/agda/agda/pull/8870#issuecomment-6396486143
open import Agda.Primitive

postulate
  I : Set
  F : (o : I → Level) (i : I) → Set (o i)

test : Set₁
test with F (λ _ → lzero)
... | _ = Set

