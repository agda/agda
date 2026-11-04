-- Andreas, 2026-11-04, issue #8888, report and test by Fredrik Bakke

-- When splitting x :^μ on constructor c : (y :^ν C) → D,
-- the new variable y has modality μ∘ν in the context,
-- but the pattern, and thus the term c y it stands for, has annotation ν.

{-# OPTIONS --cohesion --flat-split --erasure --polarity --double-check #-}

module Issue8888 where

record R : Set₁ where
  constructor r
  field A : Set

-- Cohesion.

bad : @♭ R → R
bad x@(r _) = x

data D : Set₁ where
  c : Set → D

flatData : @♭ D → D
flatData x@(c _) = x

record S : Set₁ where
  constructor s
  field @♯ A : Set

flatSharp : @♭ S → S
flatSharp x@(s _) = x

flatLam : @♭ R → R
flatLam = λ where x@(r _) → x

-- Erasure.

@0 erased : @0 R → R
erased x@(r _) = x

record W : Set₂ where
  constructor w
  field f : R

@0 erasedNested : @0 W → W
erasedNested x@(w y@(r _)) = x

-- Polarity: the scrutinee has default polarity,
-- which differs from the polarity of the constructor's argument.

data P₊ : Set₁ where
  p : @+ Set → P₊

positive : P₊ → P₊
positive x@(p _) = x

data P₊₊ : Set₁ where
  p : @++ Set → P₊₊

strictlyPositive : P₊₊ → P₊₊
strictlyPositive x@(p _) = x

data P₋ : Set₁ where
  p : @- Set → P₋

negative : P₋ → P₋
negative x@(p _) = x

-- Used to crash the double-checker, or report a mismatch; should succeed.
