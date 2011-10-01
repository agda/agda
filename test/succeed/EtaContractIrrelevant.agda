-- 2011-10-01 Andreas
module EtaContractIrrelevant where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

subst : {A : Set}(P : A → Set){a b : A} → a ≡ b → P a → P b
subst P refl x = x

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
