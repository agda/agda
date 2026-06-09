{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

foo : true ≡ false → Bool
foo p rewrite p = {!!}
