
module _ where

open import Common.Prelude renaming (_+_ to _+N_)
open import Common.Integer

diff : Nat → Nat → Integer
diff  a       zero   = pos a
diff  zero   (suc b) = negsuc b
diff (suc a) (suc b) = diff a b

_+_ : Integer → Integer → Integer
pos    a + pos    b = pos (a +N b)
pos    a + negsuc b = diff a (suc b)
negsuc a + pos    b = diff b (suc a)
negsuc a + negsuc b = negsuc (suc a +N b)

printInt : Integer → IO Unit
printInt n = putStrLn (intToString n)

main : IO Unit
main = printInt (pos 42 + pos 58)     ,,
       printInt (pos 42 + negsuc 141) ,,
       printInt (pos 42 + negsuc 31)  ,,
       printInt (negsuc 42 + pos 143) ,,
       printInt (negsuc 42 + pos 33)  ,,
       printInt (negsuc 42 + negsuc 56)
