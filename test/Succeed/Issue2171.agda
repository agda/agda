
postulate
  id : {t : Set} → t → t
  _≡_ : {t : Set} → t → t → Set
  ⊤ : Set

record FunctorOp (f : Set → Set) : Set₁ where
record FunctorLaws (f : Set → Set) {{op : FunctorOp f}} : Set₁ where

-- demand functor laws to access <*>, but promise we won't use them in our definition
record ApplyOp (A : Set → Set) {{_ : FunctorOp A}} .{{_ : FunctorLaws A}} : Set₁ where
  field
    _<*>_ : ∀ {t₁ t₂} → A (t₁ → t₂) → A t₁ → A t₂

open ApplyOp {{...}}

record ApplyLaws₂ (A : Set → Set) {{_ : FunctorOp A}} .{{_ : FunctorLaws A}} {{i : ApplyOp A}} : Set₁ where
  -- but if we try to do anything in here...
  -- resolution fails, even though our instance `i` is already resolved and in scope!

  field
    blah : ∀ (f : A (⊤ → ⊤)) → (x : A ⊤) → (f <*> x) ≡ x
