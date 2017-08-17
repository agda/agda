{-# OPTIONS --instance-search-depth=10 #-}

module _ where

module _
  {A : Set}
  (B₁ : A → Set)
  (B₂ : A → Set)
  (f : A → A)
  where
  type = ∀ {x : A} → B₁ x → B₂ (f x)
  record Class : Set where field method : type
  method : {{_ : Class}} → type
  method {{I}} = Class.method I

id : ∀ {A : Set} → A → A
id x = x

Ext : {A : Set} (B : A → Set) → A → Set
Ext B x = B x → B x

postulate

  Foo : Set

  instance

    _ : {A : Set}
        {B : A → Set}
        {{_ : Class (Ext B) (Ext B) id}}
        → Class (Ext B) (Ext (λ _ → Foo)) id

module _
  {A : Set}
  (B : A → Set)
  {{_ : Class (Ext B) (Ext B) id}}
  {y}
  (R : B y → Set)
  where

  postulate

    _ : let Point = λ (f : B y → B y) → ∀ x → R (f x) in
        Class Point Point (method (Ext _) (Ext _) id)
