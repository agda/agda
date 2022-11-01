open import Agda.Builtin.Bool

data @0 D₁ : Set where
  c₁    : D₁
  @ω c₂ : D₁

@0 _ : D₁
_ = c₁

f : D₁ → Bool
f c₁ = true
f c₂ = false

record @0 R₁ : Set where
  field
    x : D₁

  @ω y : D₁
  y = x

data @0 D₂ : Set

data D₂ where
  c : D₁ → D₂

record @0 R₂ : Set

record R₂ where
  constructor c

  @ω A : Set₁
  A = Set

  field
    -- There is no warning for this use of @ω, and the field is not
    -- erased.
    @ω x : R₁

@0 _ : R₁ → R₂
_ = c

interleaved mutual

  data @0 D₃ : Set where

  F₁ : @0 D₃ → Set₁

  data D₃ where
    c : D₃

  F₁ c = Set

interleaved mutual

  data @0 D₄ : Set where

  F₂ : D₄ → Set

  data D₄ where
    @plenty c : D₄

  F₂ c = D₄
