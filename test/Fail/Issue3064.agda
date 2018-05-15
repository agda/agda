open import Agda.Builtin.Char
open import Agda.Builtin.Sigma

CC = Σ Char λ _ → Char

Test : (c : Char) → Set
Test 'a' = CC
Test _   = CC

test : (c : Char) → Test c
test 'a' .fst = 'a'
