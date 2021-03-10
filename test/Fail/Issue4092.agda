
open import Agda.Primitive
open import Agda.Builtin.Equality

test : lzero ≡ lsuc lzero
test = refl

-- WAS: Set != Set₁
-- SHOULD BE: lzero != lsuc lzero
