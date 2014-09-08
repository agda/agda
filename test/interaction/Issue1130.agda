-- {-# OPTIONS -v tc.with:40 #-}

id : (A : Set) → A → A
id A = {!id′!}
 -- C-c C-h produces:       id′ : ∀ {A} → A
 -- when it should produce: id′ : ∀ {A} → A → A

f : (A : Set) (B : A → Set) (a : A) → B a
f A B a = {!g A a!}
  -- Before: ∀ {A} {B : A → Set} A₁ (a : A₁) → B a
  -- After:  ∀ A (a : A) {B : A → Set} → B a
