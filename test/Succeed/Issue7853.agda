-- Reported by Miëtek Bak, minimised by Naïm Camille Favier and Andreas Abel

{-# OPTIONS --show-implicit #-}

it : ∀ {A : Set} {{_ : A}} → A
it {{a}} = a

module _ (X Y : Set) where

  data U {Z : Set} : X → Y → Z → Set where
    instance
      u : ∀ {x y z} → U x y z

  module _ (Z : Set) (x : X) (y : Y) (z : Z) where

    test : (P : U x y z → Set) → P u → P it
    test P p = p

-- WAS: error: [UnequalTerms]
-- u {_} {x} {y} {z} != u {_} {x} of type
-- {y = y₁ : Y} {z = z₁ : Z} → U {Z} x y₁ z₁
-- when checking that the expression p has type
-- P (it {U {Z} x y z} ⦃ u {_} {z} ⦄)
