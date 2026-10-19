{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data D (A B : Set) : Set where
  c c' : D A B

postulate rew : c {Bool} {Bool} ≡ c' {Bool} {Bool}

{-# REWRITE rew #-}
