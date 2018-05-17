
open import Common.Prelude

test : List Char → Char
test []         = 'a'
test ('a' ∷ []) = 'b'
-- test (c ∷ cs)   = c
