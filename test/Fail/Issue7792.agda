module Issue7792 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

module M (X : Set) where
  record Foo : Set where
    no-eta-equality
    constructor inc
    field foo1 foo2 : X

  {-# INLINE Foo.constructor #-}

  open Foo

  to : X → X → Foo
  {-# INLINE to #-}
  to a b = record { foo1 = a ; foo2 = b }

module N (X : Set) where
  open M X public

open N Nat

x : Foo
x = to 1 2

_ : x ≡ inc 1 2
_ = refl
