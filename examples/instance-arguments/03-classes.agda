{-# OPTIONS --verbose tc.constr.findInScope:15 #-}

module 03-classes where

open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Data.Nat.Properties as NatProps
open import Data.Nat
open import Data.Bool.Properties using (isCommutativeSemiring-∧-∨)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary

open import Level renaming (zero to lzero; suc to lsuc)

open CommutativeSemiring NatProps.commutativeSemiring using (semiring)
open IsCommutativeSemiring isCommutativeSemiring using (isSemiring)
open IsCommutativeSemiring isCommutativeSemiring-∧-∨ using () renaming (isSemiring to Bool-isSemiring)

record S (A : Set) : Set₁ where
  field
    z : A
    o : A
    _≈_ : Rel A lzero
    _⟨+⟩_ : Op₂ A
    _⟨*⟩_ : Op₂ A
    isSemiring' : IsSemiring _≈_ _⟨+⟩_ _⟨*⟩_ z o

ℕ-S : S ℕ
ℕ-S = record { z = 0; o = 1;
               _≈_ = _≡_; _⟨+⟩_ = _+_; _⟨*⟩_ = _*_;
               isSemiring' = isSemiring }

zero' : {A : Set} → {{aRing : S A}} → A
zero' {{ARing}} = S.z ARing

zero-nat : ℕ
zero-nat = zero'

zero'' : {A : Set} {_≈_ : Rel A lzero} {_⟨+⟩_ _⟨*⟩_ : Op₂ A} {z o : A} →
         {{isr : IsSemiring _≈_ _⟨+⟩_ _⟨*⟩_ z o}} → A
zero'' {z = z} = z

zero-nat' : ℕ
zero-nat' = zero''

isZero : {A : Set} {_≈_ : Rel A lzero} {_⟨+⟩_ _⟨*⟩_ : Op₂ A} {z o : A} →
         {{isr : IsSemiring _≈_ _⟨+⟩_ _⟨*⟩_ z o}} → Zero _≈_ z _⟨*⟩_
isZero {{isr}} = IsSemiring.zero isr

useIsZero : 0 * 5 ≡ 0
useIsZero = proj₁ isZero 5
