module Epic where

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

_+_ : Nat -> Nat -> Nat
Z + m = m
S n + m = S (n + m)

_*_ : Nat -> Nat -> Nat
Z * m = Z
S n * m = m + (n * m)

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO Z #-}
{-# BUILTIN SUC S #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

data Unit : Set where
  unit : Unit

postulate
  IO         : Set -> Set
  printNat   : Nat -> IO Unit

{-# COMPILED_EPIC printNat (a : BigInt, u : Unit) -> Unit = putStrLn (bigIntToStr(a)) #-}


main : IO Unit
main = printNat (7 * 191)