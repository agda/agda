-- Andreas, 2013-10-24 Bug reported to me by Christoph-Simon Senjak
module Issue924 where

open import Level

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Data.Bool

open import Data.Maybe.Base

import Data.Nat as ℕ
open import Data.Nat using (ℕ)
import Data.Nat.Divisibility as ℕ
import Data.Nat.Properties as ℕ
open import Data.Nat.DivMod

import Data.Fin as F
open import Data.Fin using (Fin)
import Data.Fin.Properties as F

import Data.List as L
open import Data.List using (List)

open import Data.Vec

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Algebra
open import Algebra.Structures


Byte : Set
Byte = Fin 256

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
_ ^ 0 = 1
n ^ (ℕ.suc m) = n ℕ.* (n ^ m)

BitVecToNat : {n : ℕ} → Vec Bool n → ℕ
BitVecToNat [] = 0
BitVecToNat (true ∷ r) = ℕ.suc (2 ℕ.* (BitVecToNat r))
BitVecToNat (false ∷ r) = (2 ℕ.* (BitVecToNat r))

postulate ≤lem₁ : {a b : ℕ} → (a ℕ.< b) → (2 ℕ.* a) ℕ.< (2 ℕ.* b)

postulate ≤lem₂ : {a b : ℕ} → (a ℕ.< (ℕ.suc b)) → (ℕ.suc (2 ℕ.* a)) ℕ.< (2 ℕ.* (ℕ.suc b))
postulate ≤lem₃ : {a b c : ℕ} → (c ℕ.+ (a ℕ.* 2) ℕ.< (2 ℕ.* b)) → a ℕ.< b

¬0<b∧0≡b : {b : ℕ} → 0 ℕ.< b → 0 ≡ b → ⊥
¬0<b∧0≡b {0} () 0≡b
¬0<b∧0≡b {ℕ.suc n} 0<b ()

0<a∧0<b→0<ab : (a b : ℕ) → (0 ℕ.< a) → (0 ℕ.< b) → (0 ℕ.< (a ℕ.* b))
0<a∧0<b→0<ab a b 0<a 0<b with 1 ℕ.≤? (a ℕ.* b)
...                      | yes y = y
...                      | no n with (a ℕ.* b) | inspect (λ x → a ℕ.* x) b
...                             | ℕ.suc ns | _ = ⊥-elim (n (ℕ.s≤s (ℕ.z≤n {ns})))
...                             | 0 | [ eq ] with ℕ.m*n≡0⇒m≡0∨n≡0 a {b} eq
...                                          | inj₁ a≡0 = ⊥-elim (¬0<b∧0≡b 0<a (sym a≡0))
...                                          | inj₂ b≡0 = ⊥-elim (¬0<b∧0≡b 0<b (sym b≡0))

0<s^b : {a b : ℕ} → (0 ℕ.< ((ℕ.suc a) ^ b))
0<s^b {_} {0} = ℕ.s≤s ℕ.z≤n
0<s^b {m} {ℕ.suc n} = 0<a∧0<b→0<ab (ℕ.suc m) ((ℕ.suc m) ^ n) (ℕ.s≤s ℕ.z≤n) (0<s^b {m} {n})

<-lemma : (b : ℕ) → (0 ℕ.< b) → ∃ λ a → ℕ.suc a ≡ b
<-lemma (ℕ.suc b) (ℕ.s≤s (ℕ.z≤n {.b})) = ( b , refl )

2^lem₁ : (a : ℕ) → ∃ λ b → (ℕ.suc b) ≡ (2 ^ a)
2^lem₁ a = <-lemma (2 ^ a) (0<s^b {1} {a})

BitVecToNatLemma : {n : ℕ} → (s : Vec Bool n) → ((BitVecToNat s) ℕ.< (2 ^ n))
BitVecToNatLemma {0} [] = ℕ.s≤s ℕ.z≤n
BitVecToNatLemma {ℕ.suc n} (false ∷ r) = ≤lem₁ (BitVecToNatLemma r)
BitVecToNatLemma {ℕ.suc n} (true ∷ r) = ret₃ where
     q = 2^lem₁ n
     t = proj₁ q
     s : (ℕ.suc t) ≡ 2 ^ n
     s = proj₂ q
     ret₁ : (BitVecToNat r) ℕ.< (ℕ.suc t)
     ret₁ = subst (λ u → (BitVecToNat r) ℕ.< u) (sym s) (BitVecToNatLemma r)
     ret₂ : (ℕ.suc (2 ℕ.* (BitVecToNat r))) ℕ.< (2 ℕ.* (ℕ.suc t))
     ret₂ = ≤lem₂ ret₁
     ret₃ : (ℕ.suc (2 ℕ.* (BitVecToNat r))) ℕ.< (2 ^ (ℕ.suc n))
     ret₃ = subst (λ u → (ℕ.suc (2 ℕ.* (BitVecToNat r))) ℕ.< (2 ℕ.* u)) s ret₂

BitVecToFin : {n : ℕ} → Vec Bool n → Fin (2 ^ n)
BitVecToFin s = F.fromℕ< (BitVecToNatLemma s)

FinToBitVec : {n : ℕ} → (m : Fin (2 ^ n)) → ∃ λ (s : Vec Bool n) → (BitVecToFin s ≡ m)
FinToBitVec {0} F.zero = ( [] , refl )
FinToBitVec {0} (F.suc ())
FinToBitVec {ℕ.suc n} k = ( ret₁ , lem₇ ) where

  open CommutativeSemiring ℕ.+-*-commutativeSemiring using (*-comm)

  kn = F.toℕ k

  p2^n' = 2^lem₁ (ℕ.suc n)

  p2^n = proj₁ p2^n'

  p2^nl : ℕ.suc p2^n ≡ 2 ^ (ℕ.suc n)
  p2^nl = proj₂ p2^n'

  kn<2^n : kn ℕ.< 2 ^ (ℕ.suc n)
  kn<2^n = subst (λ d → kn ℕ.< d) p2^nl (subst (λ d → kn ℕ.< ℕ.suc (ℕ.pred d)) (sym p2^nl) (ℕ.s≤s (F.toℕ≤pred[n] k)))

  dm = kn divMod 2

  quot = DivMod.quotient dm

  rem = F.toℕ (DivMod.remainder dm)

  Fin2toBool : Fin 2 → Bool
  Fin2toBool F.zero = false
  Fin2toBool (F.suc F.zero) = true
  Fin2toBool (F.suc (F.suc ()))

  zl = 2^lem₁ n

  lem₀ : rem ℕ.+ quot ℕ.* 2 ℕ.< (2 ^ (ℕ.suc n))
  lem₀ = subst (λ d → d ℕ.< (2 ^ (ℕ.suc n))) (DivMod.property dm) kn<2^n

  lem₁ : (DivMod.quotient dm) ℕ.< (2 ^ n)
  lem₁ = ≤lem₃ {a = quot} {b = 2 ^ n} {c = rem} lem₀

  fQuot : Fin (2 ^ n)
  fQuot = F.fromℕ< lem₁

  -- the recursive call
  prevRet : ∃ λ (s : Vec Bool n) → (BitVecToFin s ≡ fQuot)
  prevRet = FinToBitVec (F.fromℕ< lem₁)

  prevRetEq : (BitVecToFin (proj₁ prevRet) ≡ fQuot)
  prevRetEq = proj₂ prevRet

  lem₉ : {n : ℕ} → (r : Vec Bool n) → F.toℕ (BitVecToFin r) ≡ (BitVecToNat r)
  lem₉ r = trans (cong F.toℕ refl) (F.toℕ-fromℕ< (BitVecToNatLemma r))

  prevRetEqℕ : quot ≡ BitVecToNat (proj₁ prevRet)
  prevRetEqℕ = trans (trans (sym (F.toℕ-fromℕ< lem₁)) (cong F.toℕ (sym prevRetEq))) (lem₉ (proj₁ prevRet))

  ret₁ = (Fin2toBool (DivMod.remainder dm)) ∷ (proj₁ prevRet)

  lem₃ : (r : Fin 2) → (BitVecToNat ((Fin2toBool r) ∷ (proj₁ prevRet))) ≡ (F.toℕ r) ℕ.+ (2 ℕ.* (BitVecToNat (proj₁ prevRet)))
  lem₃ F.zero = refl
  lem₃ (F.suc F.zero) = refl
  lem₃ (F.suc (F.suc ()))

  lem₅ : rem ℕ.+ (2 ℕ.* (BitVecToNat (proj₁ prevRet))) ≡ kn
  lem₅ = subst (λ d → rem ℕ.+ d ≡ kn) (*-comm (BitVecToNat (proj₁ prevRet)) 2)
         (subst (λ d → rem ℕ.+ d ℕ.* 2 ≡ kn) prevRetEqℕ (sym (DivMod.property dm)))

  lem₆ : (BitVecToNat ret₁) ≡ kn
  lem₆ =
    begin
      BitVecToNat ret₁
    ≡⟨ lem₃ (DivMod.remainder dm) ⟩
      rem ℕ.+ (2 ℕ.* (BitVecToNat (proj₁ prevRet)))
    ≡⟨ lem₅ ⟩
      kn
    ∎
  -- lem₆ = trans lem₄ lem₅

  lem₈ : kn ≡ F.toℕ (F.fromℕ< kn<2^n)
  lem₈ = sym (cong F.toℕ (F.fromℕ<-toℕ k kn<2^n))

  lem₇ : (BitVecToFin ret₁) ≡ k
  lem₇ = trans (F.toℕ-injective (trans (lem₉ ret₁) (trans lem₆ lem₈))) (F.fromℕ<-toℕ k kn<2^n)

record ByteStream : Set where
  constructor bs
  field
    cBit : Maybe (∃ λ (c : Fin 8) → Vec Bool (ℕ.suc (F.toℕ c)))
    str : List Byte
    property : (cBit ≡ nothing) → (str ≡ L.[])


byteStreamFromList : List Byte → ByteStream
byteStreamFromList L.[]      = bs nothing
                                  L.[]
                                  (λ _ → refl)
byteStreamFromList (a L.∷ x) = bs (just ((F.fromℕ 7) , (proj₁ (FinToBitVec a))))
                                  x
                                  (λ ())
-- Problem WAS:
-- Normalization in unifyConArgs went berserk when checking this
-- absurd lambda.  Fixed by more cautious normalization in unifier.
