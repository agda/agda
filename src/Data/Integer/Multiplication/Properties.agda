------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to multiplication of integers
------------------------------------------------------------------------

module Data.Integer.Multiplication.Properties where

open import Algebra
  using (module CommutativeSemiring; CommutativeMonoid)
import Algebra.FunctionProperties
open import Algebra.Structures using (IsSemigroup; IsCommutativeMonoid)
open import Data.Integer
   using (ℤ; -[1+_]; +_; ∣_∣; sign; _◃_) renaming (_*_ to ℤ*)
open import Data.Nat
  using (suc; zero) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Product using (proj₂)
import Data.Nat.Properties as ℕ
open import Data.Sign using () renaming (_*_ to _S*_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; cong; cong₂; isEquivalence)

open Algebra.FunctionProperties (_≡_ {A = ℤ})
open CommutativeSemiring ℕ.commutativeSemiring
  using (+-identity; *-comm) renaming (zero to *-zero)

------------------------------------------------------------------------
-- Multiplication and one form a commutative monoid

private
  lemma : ∀ a b c → c ℕ+ (b ℕ+ a ℕ* suc b) ℕ* suc c
                  ≡ c ℕ+ b ℕ* suc c ℕ+ a ℕ* suc (c ℕ+ b ℕ* suc c)
  lemma =
    solve 3 (λ a b c → c :+ (b :+ a :* (con 1 :+ b)) :* (con 1 :+ c)
                    := c :+ b :* (con 1 :+ c) :+
                       a :* (con 1 :+ (c :+ b :* (con 1 :+ c))))
            refl
    where open ℕ.SemiringSolver


identityˡ : LeftIdentity (+ 1) ℤ*
identityˡ (+ zero ) = refl
identityˡ -[1+  n ] rewrite proj₂ +-identity n = refl
identityˡ (+ suc n) rewrite proj₂ +-identity n = refl

comm : Commutative ℤ*
comm -[1+ a ] -[1+ b ] rewrite *-comm (suc a) (suc b) = refl
comm -[1+ a ] (+   b ) rewrite *-comm (suc a) b       = refl
comm (+   a ) -[1+ b ] rewrite *-comm a       (suc b) = refl
comm (+   a ) (+   b ) rewrite *-comm a       b       = refl

assoc : Associative ℤ*
assoc (+ zero) _ _ = refl
assoc x (+ zero) _ rewrite proj₂ *-zero ∣ x ∣ = refl
assoc x y (+ zero) rewrite
    proj₂ *-zero ∣ y ∣
  | proj₂ *-zero ∣ x ∣
  | proj₂ *-zero ∣ sign x S* sign y ◃ ∣ x ∣ ℕ* ∣ y ∣ ∣
  = refl
assoc -[1+ a  ] -[1+ b  ] (+ suc c) = cong (+_ ∘ suc) (lemma a b c)
assoc -[1+ a  ] (+ suc b) -[1+ c  ] = cong (+_ ∘ suc) (lemma a b c)
assoc (+ suc a) (+ suc b) (+ suc c) = cong (+_ ∘ suc) (lemma a b c)
assoc (+ suc a) -[1+ b  ] -[1+ c  ] = cong (+_ ∘ suc) (lemma a b c)
assoc -[1+ a  ] -[1+ b  ] -[1+ c  ] = cong -[1+_]     (lemma a b c)
assoc -[1+ a  ] (+ suc b) (+ suc c) = cong -[1+_]     (lemma a b c)
assoc (+ suc a) -[1+ b  ] (+ suc c) = cong -[1+_]     (lemma a b c)
assoc (+ suc a) (+ suc b) -[1+ c  ] = cong -[1+_]     (lemma a b c)

isSemigroup : IsSemigroup _ _
isSemigroup = record
    { isEquivalence = isEquivalence
    ; assoc         = assoc
    ; ∙-cong        = cong₂ ℤ*
    }

isCommutativeMonoid : IsCommutativeMonoid _≡_ ℤ* (+ 1)
isCommutativeMonoid = record
  { isSemigroup = isSemigroup
  ; identityˡ   = identityˡ
  ; comm        = comm
  }

commutativeMonoid : CommutativeMonoid _ _
commutativeMonoid = record
  { Carrier             = ℤ
  ; _≈_                 = _≡_
  ; _∙_                 = ℤ*
  ; ε                   = + 1
  ; isCommutativeMonoid = isCommutativeMonoid
  }
