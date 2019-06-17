{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

{-# BUILTIN REWRITE _≡_ #-}

not : Bool → Bool
not true = false
not false = true

postulate rew : Nat ≡ Bool
{-# REWRITE rew #-}

0' : Bool
0' = 0

test : not 0' ≡ true
test = refl
