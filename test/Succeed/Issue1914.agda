{-# OPTIONS -v tc.size:100 #-}
-- {-# OPTIONS -v tc.meta:100 #-}

{-# OPTIONS --sized-types #-}

open import Common.Size using (Size; Size<_)

postulate
  A : Set

record R (i₀ : Size) (x : A) : Set where
  coinductive
  field
    force : (j : Size< i₀) → R j x

postulate
  P : (A → Set) → Set
  f : (Q : A → Set) (x : A) {{ c : P Q }} → Q x → Q x
  g : (i₁ : Size) (x : A) → R i₁ x → R i₁ x

  instance
    c : {i₂ : Size} → P (R i₂)

accepted rejected : A → (x : A) (i₃ : Size) → R i₃ x → R i₃ x

accepted y x i r = g _ _ (f _ _ r)

rejected y x i r = g _ _ (f _ x r)
