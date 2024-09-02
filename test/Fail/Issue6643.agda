{-# OPTIONS --rewriting --confluence-check #-}
module Issue6643 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

{-# BUILTIN REWRITE _≡_ #-}

p : true ≡ false
q : true ≡ false
p = q
{-# REWRITE p #-}

q = refl
