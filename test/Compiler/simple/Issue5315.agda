{-# OPTIONS --erasure #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Common.IO

data D : @0 Nat → Set where
  c : ∀ {@0 n} → D (n + n)

{-# FOREIGN GHC data D = C #-}
{-# COMPILE GHC D = data D (C) #-}

data Bar : Set where
  bar : Bar

data Foo : Set where
  foo : @0 Bar → Foo

{-# FOREIGN GHC data Foo = Foo #-}
{-# COMPILE GHC Foo = data Foo (Foo) #-}

main : IO ⊤
main = return _
