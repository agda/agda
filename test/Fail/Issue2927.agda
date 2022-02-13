
{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

postulate
  P : (A : Set₁) → A → Set₁
  p : (i : Size) (f : {_ : Size< i} → Set) (x : _) →
      P ({_ : Size< i} → Set) f
