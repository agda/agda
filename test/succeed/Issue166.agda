{-# OPTIONS --sized-types #-}

module Issue166 where

postulate
  Size : Set
  ↑_   : Size → Size
  ∞    : Size

{-# BUILTIN SIZE    Size #-}
{-# BUILTIN SIZESUC ↑_   #-}
{-# BUILTIN SIZEINF ∞    #-}

data ⊥ : Set where

module M (A : Set) where

  data SizedNat : {i : Size} → Set where
    zero : {i : Size} → SizedNat {↑ i}
    suc  : {i : Size} → SizedNat {i} → SizedNat {↑ i}

module M′ = M ⊥
