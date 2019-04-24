module HOAny where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

data Wrapper (M : Set → Set) : Set where
  mnat  : M Nat → Wrapper M
  mbool : M Bool → Wrapper M

{-# FOREIGN GHC data AgdaWrapper m = Mnat (m Integer) | Mbool (m Bool) #-}
{-# COMPILE GHC Wrapper = data AgdaWrapper (Mnat | Mbool) #-}

map : ∀ {M N} → (∀ {n} → M n → N n) → Wrapper M → Wrapper N
map f (mnat mn)  = mnat (f mn)
map f (mbool mb) = mbool (f mb)

-- Higher-order use of Any in the compiled code:

-- data AgdaWrapper m = Mnat (m Integer) | Mbool (m Bool)

-- map ::
--  (() -> ()) ->
--  (() -> ()) ->
--  (() -> AgdaAny -> AgdaAny) -> AgdaWrapper AgdaAny -> AgdaWrapper AgdaAny

-- WAS:
-- The expected kind to AgdaWrapper's argument is * -> *
-- but AgdaAny's kind is *

-- WANT: SUCCESS
-- made possible by making AgdaAny poly-kinded

open import Common.Prelude

main : IO Unit
main = putStrLn ""
