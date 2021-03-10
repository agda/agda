{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

data A : Set where
  a  : A
  eq : a ≡ a

bad : ∀ i → eq i ≡ a
bad i j = eq (primIMin i (primINeg j))

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE bad #-}
