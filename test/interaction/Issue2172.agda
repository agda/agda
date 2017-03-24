-- Andreas, 2016-09-12 issue #2172
--
-- Instance search should succeed also when instance meta is supplied by the user.
--
-- This test case is not minimal, but illustrates the point.

-- {-# OPTIONS -v tc.term.args:30 -v tc.term.args.ifs:15 -v tc.meta.new:50 -v tc.meta.name:100 -v tc.term.args.named:75 #-}

module Issue2172 where

postulate
  id : {t : Set} → t → t
  _≡_ : {t : Set} → t → t → Set
  ⊤ : Set

record FunctorOp (F : Set → Set) : Set₁ where
  field
    map : ∀{A B} → (A → B) → F A → F B

record FunctorLaws (F : Set → Set) {{O : FunctorOp F}} : Set₁ where
  field
    map-id : ∀{A : Set} → FunctorOp.map O (id {A}) ≡ (id {F A})

record ApplyOp (A : Set → Set) {{O : FunctorOp A}} {{L : FunctorLaws A}} : Set₁ where
  field
    iapply : ∀ {t₁ t₂} → A (t₁ → t₂) → A t₁ → A t₂

record ApplyLaws (A : Set → Set) {{O : FunctorOp A}} {{L : FunctorLaws A}} {{i : ApplyOp A}} : Set₁ where

  open ApplyOp {{...}}
  field
    works : ∀ (f : A (⊤ → ⊤)) → (x : A ⊤) → (iapply f x) ≡ x
    -- test2 : ∀ (f : A (⊤ → ⊤)) → (x : A ⊤) → (iapply {_} {{_}} f x) ≡ x
    -- test1 : ∀ (f : A (⊤ → ⊤)) → (x : A ⊤) → (iapply {A₁ = _} {{_}} {{L₁ = _}} f x) ≡ x
    -- test0 : ∀ (f : A (⊤ → ⊤)) → (x : A ⊤) → (iapply {{L₁ = _}} f x) ≡ x
    -- test  : ∀ (f : A (⊤ → ⊤)) → (x : A ⊤) → (iapply {{L₁ = {!L!}}} f x) ≡ x
