{-# OPTIONS --cubical #-}
module ConInlineTypeAlias where

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

record Foo : Set where
  constructor mk-foo
  field
    x : Nat
    p : x ≡ 0

{-# INLINE mk-foo #-}

Foo′ : Set
Foo′ = Foo

-- Inlining constructors didn't reduce the type of the original clause,
-- making projectTyped fail, resulting in the *generated* clause having
-- no type. If the generated clause has IApply copatterns and no type,
-- IApplyConfluence throws an __IMPOSSIBLE__.

test : Foo′
test = record { x = 0 ; p = λ i → 0 }
