------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Data.Fin as Fin using (Fin; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat as Nat
open import Data.Nat.Properties as NatP
open import Data.Nat.Properties.Simple
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe
  using (erase)

open NatP.SemiringSolver
open P.≡-Reasoning
open Nat.≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩′_)

infixl 7 _div_ _mod_ _divMod_

-- A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

-- Integer division.

private

  div-helper : ℕ → ℕ → ℕ → ℕ → ℕ
  div-helper ack s zero    n       = ack
  div-helper ack s (suc d) zero    = div-helper (suc ack) s d s
  div-helper ack s (suc d) (suc n) = div-helper ack       s d n

  {-# BUILTIN NATDIVSUCAUX div-helper #-}

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(d div 0) {}
(d div suc s) = div-helper 0 s d s

-- The remainder after integer division.

private

  mod-helper : ℕ → ℕ → ℕ → ℕ → ℕ
  mod-helper ack s zero    n       = ack
  mod-helper ack s (suc d) zero    = mod-helper zero      s d s
  mod-helper ack s (suc d) (suc n) = mod-helper (suc ack) s d n

  {-# BUILTIN NATMODSUCAUX mod-helper #-}

  -- The remainder is not too large.

  mod-lemma : (ack d n : ℕ) →
              let s = ack + n in
              mod-helper ack s d n ≤ s

  mod-lemma ack zero n = start
    ack      ≤⟨ m≤m+n ack n ⟩
    ack + n  □

  mod-lemma ack (suc d) zero = start
    mod-helper zero (ack + 0) d (ack + 0)  ≤⟨ mod-lemma zero d (ack + 0) ⟩
    ack + 0                                □

  mod-lemma ack (suc d) (suc n) =
    P.subst (λ x → mod-helper (suc ack) x d n ≤ x)
            (P.sym (+-suc ack n))
            (mod-lemma (suc ack) d n)

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
(d mod 0) {}
(d mod suc s) =
  Fin.fromℕ≤″ (mod-helper 0 s d s)
              (Nat.erase (≤⇒≤″ (s≤s (mod-lemma 0 d s))))

-- Integer division with remainder.

private

  -- The quotient and remainder are related to the dividend and
  -- divisor in the right way.

  division-lemma :
    (mod-ack div-ack d n : ℕ) →
    let s = mod-ack + n in
    mod-ack + div-ack * suc s + d
      ≡
    mod-helper mod-ack s d n + div-helper div-ack s d n * suc s

  division-lemma mod-ack div-ack zero n = begin

    mod-ack + div-ack * suc s + zero  ≡⟨ +-right-identity _ ⟩

    mod-ack + div-ack * suc s         ∎

    where s = mod-ack + n

  division-lemma mod-ack div-ack (suc d) zero = begin

    mod-ack + div-ack * suc s + suc d                ≡⟨ solve 3
                                                              (λ mod-ack div-ack d →
                                                                   let s = mod-ack :+ con 0 in
                                                                   mod-ack :+ div-ack :* (con 1 :+ s) :+ (con 1 :+ d)
                                                                     :=
                                                                   (con 1 :+ div-ack) :* (con 1 :+ s) :+ d)
                                                              P.refl mod-ack div-ack d ⟩
    suc div-ack * suc s + d                          ≡⟨ division-lemma zero (suc div-ack) d s ⟩

    mod-helper zero          s      d  s    +
    div-helper (suc div-ack) s      d  s    * suc s  ≡⟨⟩

    mod-helper      mod-ack  s (suc d) zero +
    div-helper      div-ack  s (suc d) zero * suc s  ∎

    where s = mod-ack + 0

  division-lemma mod-ack div-ack (suc d) (suc n) = begin

    mod-ack + div-ack * suc s + suc d                   ≡⟨ solve 4
                                                                 (λ mod-ack div-ack n d →
                                                                      mod-ack :+ div-ack :* (con 1 :+ (mod-ack :+ (con 1 :+ n))) :+ (con 1 :+ d)
                                                                        :=
                                                                      con 1 :+ mod-ack :+ div-ack :* (con 2 :+ mod-ack :+ n) :+ d)
                                                                 P.refl mod-ack div-ack n d ⟩
    suc mod-ack + div-ack * suc s′ + d                  ≡⟨ division-lemma (suc mod-ack) div-ack d n ⟩

    mod-helper (suc mod-ack) s′ d n +
    div-helper      div-ack  s′ d n * suc s′            ≡⟨ P.cong (λ s → mod-helper (suc mod-ack) s d n +
                                                                         div-helper div-ack s d n * suc s)
                                                                  (P.sym (+-suc mod-ack n)) ⟩

    mod-helper (suc mod-ack) s d n +
    div-helper      div-ack  s d n * suc s              ≡⟨⟩

    mod-helper      mod-ack  s (suc d) (suc n) +
    div-helper      div-ack  s (suc d) (suc n) * suc s  ∎

    where
    s  = mod-ack + suc n
    s′ = suc mod-ack + n

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
(d divMod 0) {}
(d divMod suc s) =
  result (d div suc s) (d mod suc s) (TrustMe.erase (begin
    d                                                        ≡⟨ division-lemma 0 0 d s ⟩
    mod-helper 0 s d s         + div-helper 0 s d s * suc s  ≡⟨ P.cong₂ _+_ (P.sym (FinP.toℕ-fromℕ≤ lemma)) P.refl ⟩
    toℕ (Fin.fromℕ≤    lemma)  + div-helper 0 s d s * suc s  ≡⟨ P.cong (λ n → toℕ n + div-helper 0 s d s * suc s)
                                                                       (FinP.fromℕ≤≡fromℕ≤″ lemma _) ⟩
    toℕ (Fin.fromℕ≤″ _ lemma′) + div-helper 0 s d s * suc s  ∎))
  where
  lemma  = s≤s (mod-lemma 0 d s)
  lemma′ = Nat.erase (≤⇒≤″ lemma)
