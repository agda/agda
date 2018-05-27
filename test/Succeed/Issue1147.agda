-- 2014-05-26 Andrea & Andreas, AIM XIX
-- Too eager pruning

module Succeed.Issue1147 where

open import Common.Equality
open import Common.Product
open import Common.Prelude

postulate
  A : Set

if_then_else1_ : ∀ {A : Set1} → Bool → A → A → A
if true  then t else1 f = t
if false then t else1 f = f

test1 : let H : Set; H = _; M : Bool -> Set → Set; M = _ in {z : Set} → H ≡ (M true z) × M ≡ (\ b z → if b then A else1 z)
test1 = refl , refl


test2 : let H : Set; H = _; M : (Bool -> Bool) -> Set → Set; M = _ in {z : Set} → H ≡ (M (\ _ -> true) z) × M ≡ (\ b z → if b true then A else1 z)
test2 = refl , refl

test3 : let H : Set; H = _; M : (Bool × Bool) -> Set → Set; M = _ in {z : Set} {b : Bool} → H ≡ (M (true , b) z) × M ≡ (\ b z → if proj₁ b then A else1 z)
test3 = refl , refl

-- Also for defined functions

fun : Bool → Bool
fun true  = true
fun false = false

works4 : let H : Set; H = _; M : (Bool -> Bool) -> Set → Set; M = _ in {z : Set} → M ≡ (\ b z → if b true then A else1 z) × H ≡ (M fun z)
works4 = refl , refl

test4 : let H : Set; H = _; M : (Bool -> Bool) -> Set → Set; M = _ in {z : Set} → H ≡ (M fun z) × M ≡ (\ b z → if b true then A else1 z)
test4 = refl , refl
