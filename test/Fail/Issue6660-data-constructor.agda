{-# OPTIONS --guardedness #-}

open import Agda.Builtin.String
open import Agda.Builtin.Unit

data Unit : Set where
    ttt : Unit

-- This pragma is expected to fail with an error
{-# INLINE ttt #-}

f : Unit
f = ttt
