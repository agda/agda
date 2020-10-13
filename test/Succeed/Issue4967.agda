
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (_<_ to natLessThan)
open import Agda.Builtin.Int

_<_ : Int -> Int -> Bool
_<_ = \ where
  (pos m) (pos n) -> natLessThan m n
  (negsuc m) (negsuc n) -> natLessThan n m
  (negsuc _) (pos _) -> true
  (pos _) (negsuc _) -> false
{-# INLINE _<_ #-}

check : Int -> Bool
check n = pos 0 < n
