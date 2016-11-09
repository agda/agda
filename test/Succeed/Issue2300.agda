{-# OPTIONS --rewriting -v rewriting:80 #-}

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

postulate
  A : Set
  f : A → A
  h : .A → A → A
  rew : ∀ {x} → h x x ≡ x

{-# REWRITE rew #-}

test2 : (x y : A) → h x y ≡ y
test2 x y = refl
