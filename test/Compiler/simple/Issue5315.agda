{-# OPTIONS --erasure #-}

open import Agda.Builtin.Nat

data D : @0 Nat → Set where
  c : ∀ {@0 n} → D (n + n)

{-# FOREIGN GHC data D n = C #-}
{-# COMPILE GHC D = data D (C) #-}

data Bar : Set where
  bar : Bar

data Foo : Set where
  foo : @0 Bar → Foo

{-# FOREIGN GHC data Foo = Foo #-}
{-# COMPILE GHC Foo = data Foo (Foo) #-}

open import Common.Bool
open import Common.IO
open import Common.Unit

main : IO Unit
main = printBool true
