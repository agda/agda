-- Reported by Andrea, 2014-05-xx
-- We cannot prune from a meta if one of its arguments is a lambda.
-- (In some cases we could, but it is hard to get this right,
--  probably needs a flow analysis.)
-- {-# OPTIONS -v tc.meta.assign:25 -v tc.meta.kill:40 #-}

open import Common.Equality
open import Common.Product

postulate
  F : Set → Set
  A : Set

test : let H : Set
           H = _
           M : ((Set → Set) → Set) → Set
           M = _
       in {Z : Set} → H   ≡ F (M (\ G → A → G Z))
                     × F H ≡ F (F (A → A))
                     × M   ≡ \ K → K (\ _ → A)
test = refl
     , refl
     , refl


#1 : {A : Set} →
     let H : Set
         H = _
         M : (Set → Set) → Set → Set
         M = _
     in {Z : Set} → H ≡ F (M (\ _ → A) Z)
                   × M ≡ (\ F X → F X)
#1 = refl , refl

