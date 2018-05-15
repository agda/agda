open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.Equality

postulate
  A B : Set
  b : B

f : List A → Char → B
f _ 'a' = b
f [] _  = b
f _  _  = b

test : ∀ xs → f xs 'a' ≡ b
test _ = refl
