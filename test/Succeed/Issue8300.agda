-- Andreas, 2026-01-02, issue #8300
-- Report and testcase by Soares

-- {-# OPTIONS --without-K #-}
-- {-# OPTIONS -v tc.with:40 #-}
-- {-# OPTIONS -v tc.infer:40 #-}
-- {-# OPTIONS -v tc.term.def:40 #-}

module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

cong : ∀ {A B : Set} {a1 a2 : A} (f : A → B) → (a1 ≡ a2) → (f a1 ≡ f a2)
cong f refl = refl

record HasEqCode (A : Set) : Set1 where
    field
        _=#_ : A → A → Set
        en#  : ∀ a1 {a2} → (a1 ≡ a2) → (a1 =# a2)
        de#  : ∀ a1 {a2} → (a1 =# a2) → (a1 ≡ a2)
        re#  : ∀ a1 {a2} (e : a1 ≡ a2) → de# a1 (en# a1 e) ≡ e
open HasEqCode {{...}} public

data _~_ : Nat → Nat → Set where
    zero= : zero ~ zero
    suc=  : ∀ {i j} → (i ~ j) → (suc i ~ suc j)

test : HasEqCode Nat
test ._=#_ = _~_

test .de# = decode where
    decode : ∀ i {j : Nat} → (i ~ j) → (i ≡ j)
    decode zero    zero=     = refl
    decode (suc i) (suc= ij) = cong suc (decode i ij)

test .en# = encode where
    encode : ∀ i {j : Nat} → (i ≡ j) → (i ~ j)
    encode zero    refl = zero=
    encode (suc i) refl = suc= (encode i refl)

test .re# = retract where
    retract : ∀ i {j : Nat} (e : i ≡ j) → test .de# i (test .en# i e) ≡ e
    retract zero    refl = refl
    retract (suc i) refl
        with test .de# i (test .en# i refl)
               -- Inference for the postfix instance projections
               -- did not work correctly because appView
               -- would convert this to `de# test ...` rather than
               -- `de# {{test}} ...`.
           | retract i refl
    ... | _ | refl = refl

-- Should succeed.
