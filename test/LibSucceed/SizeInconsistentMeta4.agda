-- Andreas, 2012-02-24 example by Ramana Kumar
{-# OPTIONS --sized-types #-}
-- {-# OPTIONS --show-implicit -v tc.size.solve:20 -v tc.conv.size:15 #-}
module SizeInconsistentMeta4 where

open import Data.Nat using (ℕ;zero;suc) renaming (_<_ to _N<_)
open import Data.Product using (_,_;_×_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-transitive)
open import Data.List using (List)
open import Data.List.Relation.Binary.Lex.Strict using (Lex-<) renaming (<-transitive to Lex<-trans)
open import Relation.Binary using (Rel;_Respects₂_;Transitive;IsEquivalence)

open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)

import Level
open import Size using (Size;↑_)

-- keeping the definition of Vec for the positivity check
infixr 5 _∷_
data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

{- produces different error
data Lex-< {A : _} (_≈_ _<_ : Rel A Level.zero) : Rel (List A) Level.zero where
postulate
  Lex<-trans : ∀ {P _≈_ _<_} →
               IsEquivalence _≈_ → _<_ Respects₂ _≈_ → Transitive _<_ →
               Transitive (Lex-< _≈_ _<_)
-}

postulate
  N<-trans : Transitive _N<_
  -- Vec : ∀ {a} (A : Set a) → ℕ → Set a
  Vec→List : ∀ {a n} {A : Set a} → Vec A n → List A

data Type : {z : Size} → Set where
  TyApp : {z : Size} (n : ℕ) → (as : Vec (Type {z}) n) → Type {↑ z}

infix 4 _<_
data _<_ : {z : Size} → Rel (Type {z}) Level.zero where
  TyApp<TyApp : ∀ {z} {n₁} {as₁} {n₂} {as₂} → ×-Lex _≡_ _N<_ (Lex-< _≡_ (_<_ {z})) (n₁ , Vec→List as₁) (n₂ , Vec→List as₂) → _<_ {↑ z} (TyApp n₁ as₁) (TyApp n₂ as₂)

<-trans : {z : Size} → Transitive (_<_ {z})
<-trans (TyApp<TyApp p) (TyApp<TyApp q) = TyApp<TyApp (×-transitive PropEq.isEquivalence (PropEq.resp₂ _N<_) N<-trans {_≤₂_ = Lex-< _≡_ _<_ } (Lex<-trans PropEq.isEquivalence (PropEq.resp₂ _<_) <-trans) p q)
