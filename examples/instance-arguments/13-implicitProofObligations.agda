{-# OPTIONS --universe-polymorphism #-}

module 13-implicitProofObligations where

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat
open import Data.Fin using (Fin; toℕ)
open import Data.Product using (_×_; _,_)
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality
open import Function

postulate
  d : ℕ
  d≢0 : d ≢ 0
--  d≢0' : d ≢ 0

fromWitnessFalse : ∀ {p} {P : Set p} {Q : Dec P} → ¬ P → False Q
fromWitnessFalse {Q = yes p} ¬P = ⊥-elim $ ¬P p
fromWitnessFalse {Q = no ¬p} ¬P = tt

⋯ : {A : Set} → {{v : A}} → A
⋯ {{v}} = v

_divMod′_ : (dividend divisor : ℕ) {{ ≢0 : divisor ≢ 0 }} → ℕ × ℕ
a divMod′ d with _divMod_ a d { fromWitnessFalse ⋯ }
._ divMod′ d | (result q r) = q , toℕ r

_div′_ : (dividend divisor : ℕ) {{ ≢0 : divisor ≢ 0 }} → ℕ
a div′ b with a divMod′ b
a div′ b | (q , _) = q

--Agda can't resolve hiddens
-- test : {d≢0 : False (d ≟ 0)} → ℕ
-- test = 5 div d
-- test2 : {{d≢0 : d ≢ 0}} → ℕ
-- test2 = 5 div′ d

test3 = 5 div 2
test4 = 5 div′ 2
  where nz : 2 ≢ 0
        nz ()
