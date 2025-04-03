module NestedRecConstrInline where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record Foo : Set where
  constructor inc
  field foo1 foo2 : Nat

record Bar : Set where
  no-eta-equality
  constructor inc
  field
    foo  : Foo
    bar3 : Nat

record make : Set where
  constructor inc
  field
    foo1 foo2 bar3 : Nat

open Foo
open Bar
open make

{-# INLINE Bar.constructor #-}

-- This function is not turned into a copattern match, because it is
-- marked INLINE
to : make → Bar
{-# INLINE to #-}

to f = record { foo = record { foo1 = f .foo1 ; foo2 = f .foo2 } ; bar3 = f .bar3 }

-- ... so this works:
_ : to (inc 1 2 3) ≡ inc (inc 1 2) 3
_ = refl

-- And here we inline 'to' in the RHS of x, which then becomes a record
-- constructor, and *that* constructor gets inlined
x : Bar
x = to record where
  foo1 = 1
  foo2 = 2
  bar3 = 3

-- ... so this fails (x ≠ ...):
_ : x ≡ inc (inc 1 2) 3
_ = refl
