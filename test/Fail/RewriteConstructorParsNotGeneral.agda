{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

data D (A : Set) : Set where
  c c' : D A

postulate rew : c {Bool} ≡ c' {Bool}

{-# REWRITE rew #-}
