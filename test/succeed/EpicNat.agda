
data Nat : Set where
  Z : Nat
  S : Nat → Nat

_+_ : Nat → Nat → Nat
Z + m = m
S n + m = S (n + m)

_*_ : Nat → Nat → Nat
Z * m = Z
S n * m = m + (n * m)

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

data Unit : Set where
  unit : Unit

postulate
  IO          : Set → Set
  String      : Set
  natToString : Nat → String
  putStr      : String → IO Unit

printNat : Nat → IO Unit
printNat n = putStr (natToString n)

{-# COMPILED_TYPE IO IO #-}

{-# COMPILED_EPIC natToString (n : Any) -> String = bigToStr(n) #-}
{-# COMPILED_EPIC putStr (a : String, u : Unit) -> Unit = foreign Int "wputStr" (a : String); primUnit #-}


main : IO Unit
main = printNat (7 * 191)

-- should print 1337
