{-# OPTIONS --rewriting #-}
{-# OPTIONS --no-fast-reduce #-}

open import Agda.Builtin.Equality
{-# BUILTIN REWRITE _≡_ #-}

data A : Set where
  a b : A

postulate rew : a ≡ b
{-# REWRITE rew #-}

test : a ≡ b
test = refl
