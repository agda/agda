-- Andreas, 2012-01-10
-- {-# OPTIONS -v tc.constr.findInScope:50 #-}
module InstanceGuessesMeta2 where

open import Common.Level

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

record takeClass {a} 
  (F : Set a → Set a) 
  (G : Set a → ℕ → Set a) : Set (lsuc a) where
  field
    take : {A : Set a} → (n : ℕ) → F A → G A n

take : ∀ {a} {A : Set a} {F : Set a → Set a} {G : Set a → ℕ → Set a}
   {{takeA : takeClass F G}} → 
   (n : ℕ) → F A → G A n
take {{takeA}} = takeClass.take takeA

postulate 
  List : ∀ {a} → Set a → Set a
  BVec : ∀ {a} → Set a → ℕ → Set a
  toList : ∀ {a}{A : Set a}{n : ℕ} → BVec A n → List A
  -- universe polymorphic instance
  takeInstanceList : {a : Level} → takeClass (List {a = a}) BVec

take0 : {A : Set} → List A → BVec A zero
take0 l = take zero l

take1 : {A : Set} → List A → List A
take1 l = toList (take (suc zero) l) 
