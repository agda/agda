{-# OPTIONS --rewriting #-}

postulate
  _≡_ : {A : Set₁} (a : A) → A → Set
{-# BUILTIN REWRITE _≡_ #-}

record ⊤ : Set where
  constructor ★

postulate
  X Y : Set
  F : Set → Set
  FX : F X ≡ ⊤
{-# REWRITE FX #-}

postulate
  G : F X → Set
  G1 : (A : Set) → F A ≡ G ★
  G2 : G ★ ≡ Y

{-# REWRITE G1 #-}
{-# REWRITE G2 #-}
