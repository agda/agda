-- {-# OPTIONS -v tc.polarity:15 #-}
{-# OPTIONS --sized-types #-}

module Issue166 where

open import Common.Size
open import Common.Prelude

module M (A : Set) where

  data SizedNat : {i : Size} → Set where
    zero : {i : Size} → SizedNat {↑ i}
    suc  : {i : Size} → SizedNat {i} → SizedNat {↑ i}

module M′ = M ⊥
