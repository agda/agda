{-# OPTIONS --rewriting #-}
module Issue8710 where
open import Agda.Builtin.Equality
import Issue8710.A as A
import Issue8710.B as B

postulate
  A : Set
  x y : A
  s : B.S x y
  {-# REWRITE s #-}

_ : x ≡ y
_ = refl
