-- 2010-09-24
-- example originally stolen from Andrea Vezzosi's post on the Agda list 

{-# OPTIONS --no-irrelevant-projections #-}

module IrrelevantRecordFields where

-- import Common.Irrelevance  
  
infix 4 _≡_ 

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

sym : {A : Set}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

record SemiG : Set1 where
 constructor _,_,_,_,_,_
 field
   M    : Set
   unit : M
   _+_  : M -> M -> M
   .assoc     : ∀ {x y z} ->  x + (y + z) ≡ (x + y) + z
   .leftUnit  : ∀ {x} -> unit + x ≡ x
   .rightUnit : ∀ {x} -> x + unit ≡ x

dual : SemiG -> SemiG
dual (M , e , _+_ , assoc , leftUnit , rightUnit) = 
  M , e , (λ x y -> y + x) , sym assoc , rightUnit , leftUnit

data _≡₁_ {A : Set1}(a : A) : A -> Set where
  refl : a ≡₁ a

open SemiG

-- trivId : ∀ (M : SemiG) -> M ≡₁ M
-- trivId M = refl 

dual∘dual≡id : ∀ M -> dual (dual M) ≡₁ M
dual∘dual≡id M = refl {a = M}


 
