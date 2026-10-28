-- https://github.com/agda/agda/pull/8870#issuecomment-6396486143
{-# OPTIONS --rewriting #-}
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  I : Set
  g : Level → I → Level

module _ (a : Level) where
  postulate p : ∀ {i} → g a i ≡ lzero
  {-# REWRITE p #-}

  postulate
    F : (b : Level) (i : I) → Set (g b i)
    G : (b : Level) (X Y : (i : I) → Set (g b i)) → Set

  test : (b : Level) → G b (F b) (F b) ≡ G b (F b) (λ i → F b i)
  test b = refl
