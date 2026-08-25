{-# OPTIONS --cubical --safe #-}

-- Andreas, 2026-08-25, issue #8683, variant without `with`.
-- The first argument of the reflection primitive `unify` is elaborated in
-- inference mode, which used to skip the side conditions of the
-- cubical primitives.

open import Agda.Primitive using (lzero)
open import Agda.Primitive.Cubical
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

vis : Term → Arg Term
vis = arg (arg-info visible (modality relevant quantity-ω))

hid : Term → Arg Term
hid = arg (arg-info hidden (modality relevant quantity-ω))

-- The reflected term  primHComp {lzero} {Nat} {var n} (λ i o → 0) 1.
-- Its base 1 disagrees with its side (constantly 0) on var n,
-- so this must be rejected.
badTerm : Nat → Term
badTerm n = def (quote primHComp)
  ( hid (def (quote lzero) [])
  ∷ hid (def (quote Nat) [])
  ∷ hid (var n [])
  ∷ vis (lam visible (abs "i" (lam visible (abs "o" (lit (nat 0))))))
  ∷ vis (lit (nat 1))
  ∷ [] )

macro
  bad : Term → TC ⊤
  bad hole = unify (badTerm 0) hole

f : I → Nat
f j = bad
