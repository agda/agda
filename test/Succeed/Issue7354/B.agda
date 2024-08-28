
{-# OPTIONS --safe #-}
module Issue7354.B where

open import Issue7354.A

funny : ∀{X T : Set} → bleh {lzero} X T → bleh {lzero} X T
funny {X}{T} (f , g) =
  let res = f , g
  in res
