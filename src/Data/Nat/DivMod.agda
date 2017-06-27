------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Data.Fin as Fin using (Fin; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe
  using (erase)

open import Agda.Builtin.Nat using ( div-helper; mod-helper )

open SemiringSolver
open P.≡-Reasoning
open ≤-Reasoning
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

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(d div 0) {}
(d div suc s) = div-helper 0 s d s

-- The remainder after integer division.

private
  -- The remainder is not too large.

  mod-lemma : (acc d n : ℕ) →
              let s = acc + n in
              mod-helper acc s d n ≤ s

  mod-lemma acc zero n = start
    acc      ≤⟨ m≤m+n acc n ⟩
    acc + n  □

  mod-lemma acc (suc d) zero = start
    mod-helper zero (acc + 0) d (acc + 0)  ≤⟨ mod-lemma zero d (acc + 0) ⟩
    acc + 0                                □

  mod-lemma acc (suc d) (suc n) =
    P.subst (λ x → mod-helper (suc acc) x d n ≤ x)
            (P.sym (+-suc acc n))
            (mod-lemma (suc acc) d n)

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
    (mod-acc div-acc d n : ℕ) →
    let s = mod-acc + n in
    mod-acc + div-acc * suc s + d
      ≡
    mod-helper mod-acc s d n + div-helper div-acc s d n * suc s

  division-lemma mod-acc div-acc zero n = begin

    mod-acc + div-acc * suc s + zero  ≡⟨ +-right-identity _ ⟩

    mod-acc + div-acc * suc s         ∎

    where s = mod-acc + n

  division-lemma mod-acc div-acc (suc d) zero = begin

    mod-acc + div-acc * suc s + suc d                ≡⟨ solve 3
                                                              (λ mod-acc div-acc d →
                                                                   let s = mod-acc :+ con 0 in
                                                                   mod-acc :+ div-acc :* (con 1 :+ s) :+ (con 1 :+ d)
                                                                     :=
                                                                   (con 1 :+ div-acc) :* (con 1 :+ s) :+ d)
                                                              P.refl mod-acc div-acc d ⟩
    suc div-acc * suc s + d                          ≡⟨ division-lemma zero (suc div-acc) d s ⟩

    mod-helper zero          s      d  s    +
    div-helper (suc div-acc) s      d  s    * suc s  ≡⟨⟩

    mod-helper      mod-acc  s (suc d) zero +
    div-helper      div-acc  s (suc d) zero * suc s  ∎

    where s = mod-acc + 0

  division-lemma mod-acc div-acc (suc d) (suc n) = begin

    mod-acc + div-acc * suc s + suc d                   ≡⟨ solve 4
                                                                 (λ mod-acc div-acc n d →
                                                                      mod-acc :+ div-acc :* (con 1 :+ (mod-acc :+ (con 1 :+ n))) :+ (con 1 :+ d)
                                                                        :=
                                                                      con 1 :+ mod-acc :+ div-acc :* (con 2 :+ mod-acc :+ n) :+ d)
                                                                 P.refl mod-acc div-acc n d ⟩
    suc mod-acc + div-acc * suc s′ + d                  ≡⟨ division-lemma (suc mod-acc) div-acc d n ⟩

    mod-helper (suc mod-acc) s′ d n +
    div-helper      div-acc  s′ d n * suc s′            ≡⟨ P.cong (λ s → mod-helper (suc mod-acc) s d n +
                                                                         div-helper div-acc s d n * suc s)
                                                                  (P.sym (+-suc mod-acc n)) ⟩

    mod-helper (suc mod-acc) s d n +
    div-helper      div-acc  s d n * suc s              ≡⟨⟩

    mod-helper      mod-acc  s (suc d) (suc n) +
    div-helper      div-acc  s (suc d) (suc n) * suc s  ∎

    where
    s  = mod-acc + suc n
    s′ = suc mod-acc + n

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
