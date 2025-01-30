-- Reported by noughtmare

open import Agda.Builtin.Char

postulate
  A : Set
  a : A

B : A → Set
f : (x : A) → B x → A

B = _
f _ 'a' = a
f _ _ = a
