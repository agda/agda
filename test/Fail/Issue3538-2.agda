{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

data D : Set₁ where
  c : Set → D

unD : D → Set
unD (c X) = X

id : unD (c (Nat → Nat))
id x = x

postulate rew : c (Nat → Nat) ≡ c (Nat → Bool)
{-# REWRITE rew #-}

0' : Bool
0' = id 0
