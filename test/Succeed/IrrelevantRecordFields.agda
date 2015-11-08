-- 2010-09-24
-- example originally stolen from Andrea Vezzosi's post on the Agda list

{-# OPTIONS --no-irrelevant-projections #-}

module IrrelevantRecordFields where

open import Common.Equality

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

open SemiG

-- trivId : ∀ (M : SemiG) -> M ≡ M
-- trivId M = refl

dual∘dual≡id : ∀ M -> dual (dual M) ≡ M
dual∘dual≡id M = refl {x = M}
