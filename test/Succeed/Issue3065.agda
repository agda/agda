-- Jesper, 2018-05-17: Fixed internal error.  Now the second clause is
-- marked as unreachable (which is perhaps reasonable) and the first
-- clause is marked as not satisfying --exact-split (which is perhaps
-- unreasonable). To fix this properly, we would need to keep track of
-- excluded literals for not just pattern variables but also dot
-- patterns (and perhaps in other places as well).

open import Agda.Builtin.Char
open import Agda.Builtin.Equality

test : (c : Char) → c ≡ 'a' → Set
test 'a' _ = Char
test .'a' refl = Char
