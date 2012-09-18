-- 2011-10-01 Andreas
{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.polarity:15 -v tc.pos.args:10 #-}
module EtaContractIrrelevant where

import Common.Level

data _≡_ {a}{A : Set a}(x : A) : A → Set where
  refl : x ≡ x

subst : ∀ {a b}{A : Set a}(P : A → Set b){x y : A} → x ≡ y → P x → P y
subst P refl h = h

postulate
  Val : Set

Pred = Val → Set

fam : Pred → Set1
fam A = {a : Val} → .(A a) → Pred

postulate
  π : (A : Pred)(F : fam A) → Pred

πCong : {A A' : Pred}(A≡A' : A ≡ A') →
  {F  : fam A }
  {F' : fam A'}
  (F≡F' : (λ {a} Aa → F {a = a} Aa)
        ≡ (λ {a} Aa → F' {a = a} (subst (λ A → A a) A≡A' Aa))) →
  π A F ≡ π A' F'
πCong refl refl = refl
-- needs eta-contraction for irrelevant functions F F'
