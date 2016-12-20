-- Andreas, 2016-11-02, issue #2285 raised by effectfully, found by dnkndnts

-- {-# OPTIONS -v tc.data.fits:15 #-}
-- {-# OPTIONS -v tc.conv.sort:30 #-}
-- {-# OPTIONS -v tc.meta.assign:50 #-}
-- {-# OPTIONS -v tc.meta.new:50 #-}
-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.data:100 #-}

mutual
  Type = _

  data Big : Type where
    big : (∀ {α} → Set α) → Big

-- Problem WAS:
-- new sort meta _0 : .Agda.Primitive.Level
-- new meta (?0) _1 : Set _0
-- new sort meta _2 : .Agda.Primitive.Level
-- solving _0 := .Agda.Primitive.lsuc _2
-- solving _1 := Set _2
-- solving _2 := Setω

-- Big should be rejected

-- Even with Type = Setω : Setω, we do not get Hurkens through:
{-
  ⊥ : Type
  ⊥ = (A : Type) → A

  ¬_ : Type → Type
  ¬ A = A → ⊥

  -- We have some form of Type : Type
  P : Type → Type
  P A = A → Type

  U : Type
  U = (X : Type) → (P (P X) → X) → P (P X)

  test : Type
  test = P (P U) → U

{-

  -- This is not accepted:
  τ : P (P U) → U
  τ = λ (t : P (P U)) (X : Type) (f : P (P X) → X) (p : P X) → t λ x → p (f (x X f))

  σ : U → (P (P U))
  σ = λ (s : U) → s U λ t → τ t

  Δ : P U
  Δ = \y → ¬ ((p : P U) → σ y p → p (τ (σ y)))

  Ω : U
  Ω = τ \p → (x : U) → σ x p → p x

  D : Type
  D = (p : P U) → σ Ω p → p (τ (σ Ω))

  lem₁ : (p : P U) → ((x : U) → σ x p → p x) → p Ω
  lem₁ p H1 = H1 Ω \x → H1 (τ (σ x))

  lem₂ : ¬ D
  lem₂ = lem₁ Δ \x H2 H3 → H3 Δ H2 \p → H3 \y → p (τ (σ y))

  lem₃ : D
  lem₃ p = lem₁ \y → p (τ (σ y))

  loop : ⊥
  loop = lem₂ lem₃
-- -}
-- -}
