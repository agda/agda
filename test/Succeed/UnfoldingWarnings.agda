module UnfoldingWarnings where

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality

opaque
  foo : Nat → Nat
  foo x = suc x

  bar : Nat → Nat
  bar x = suc x

opaque unfolding (foo ; bar) where
  baz : ∀ x → foo x ≡ suc x
  baz x = refl

opaque unfolding (foo ; bar ; baz) where
  baz′ : ∀ x → foo x ≡ suc x
  baz′ x = refl

test : Nat
test = 0

abstract
  quux : Nat
  quux = 0

opaque
  some-other : Nat
  some-other = 0

opaque unfolding (quux ; bar ; foo ; baz ; baz′ ; asdf ; ghij ; some-other) where
  asdf : Nat
  asdf = 0

  ghij : Nat
  ghij = 0

opaque unfolding (test ; quux ; bar ; foo ; baz ; asdf) where
  _ : Nat
  _ = 0

opaque unfolding (foo ; baz) where
  _ : Nat
  _ = 0
