module IndexOnBuiltin where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

f : Fin 2 -> Fin 1
f fz     = fz
f (fs i) = i

