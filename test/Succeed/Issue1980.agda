{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

funny : true ≡ false → true ≡ false
funny x = x

{-# REWRITE funny #-}
