-- Andreas, 2012-09-17 documenting an internal error in InternalToAbstract.hs
-- {-# OPTIONS -v syntax.reify.con:30 -v tc.with.type:30 #-}
module NameFirstIfHidden where

Total : (D : (A : Set) → A → Set)(A : Set) → Set
Total D A = forall a → D A a

data D (A : Set) : (a : A) → Set where
  c : Total D A

postulate P : {A : Set}{a : A} → D A a → Set

f : (A : Set)(a : A) → P (c a) → D A a
f A a p with Total
... | _ = c a
-- should succeed, triggered an internal error before
