module Prelude.Level where

open import Agda.Primitive public
  using    (Level)
  renaming (lzero to zero; lsuc to suc; _⊔_ to max)
