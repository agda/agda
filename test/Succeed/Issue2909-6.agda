{-# OPTIONS --no-main --erasure #-}
-- {-# OPTIONS -v compile.haskell.pragma:40 #-}

postulate
  ∞  : ∀ {@0 a} (A : Set a) → Set a
  ♯_ : ∀ {@0 a} {A : Set a} → A → ∞ A
  ♭  : ∀ {@0 a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

{-# COMPILE GHC ♭ = undefined #-}
