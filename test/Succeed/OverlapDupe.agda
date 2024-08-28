module OverlapDupe where

open import Agda.Builtin.Nat
open import Agda.Primitive

postulate
  Foo : (l : Level) → Set → Set

  instance
    foo-nat : ∀ {ℓ} → Foo ℓ Nat
    foo-any : ∀ {A : Set} → Foo lzero A

  {-# INCOHERENT foo-any #-}

instance
  foo-nat' : ∀ {ℓ} → Foo ℓ Nat
  foo-nat' = foo-nat

auto : ∀ {ℓ} {A : Set ℓ} ⦃ _ : A ⦄ → A
auto ⦃ x ⦄ = x

{-

Note:

  Does foo-nat' specialise foo-any?
    => NOT specialisation

Therefore:

  instances after resolving overlap:
  - foo-nat' : {ℓ : Level} → Foo ℓ Nat
  - foo-nat : {ℓ : Level} → Foo ℓ Nat
  - INCOHERENT foo-any : {A : Set} → Foo lzero A

But foo-nat and foo-nat' are the same candidate, so according to the
rule

> There is exactly one non-incoherent candidate, along with some number of
> incoherent candidates. The non-incoherent candidate is chosen.

we should choose foo-nat; hence incoherent candidates being sunk to the
bottom and dealt with by dropSameCandidate.
-}

_ : Foo lzero Nat
_ = auto
