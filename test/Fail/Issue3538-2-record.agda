{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

record R : Set₁ where
  constructor c
  field unD : Set

open R

id : unD (c (Nat → Nat))
id x = x

postulate rew : c (Nat → Nat) ≡ c (Nat → Bool)
{-# REWRITE rew #-}
