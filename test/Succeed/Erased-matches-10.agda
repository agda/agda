-- If the K rule is on, then --erased-matches without options enables
-- all kinds of erased matches.

{-# OPTIONS --erased-matches #-}

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  p      : Level
  @0 A   : Set _
  @0 x y : A

data ⊥ : Set where

⊥-elim : @0 ⊥ → A
⊥-elim ()

data D : Set where
  c : D → D

F : @0 D → Set₁
F (c _) = Set

subst : (@0 P : A → Set p) → @0 x ≡ y → P x → P y
subst _ refl p = p
