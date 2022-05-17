{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

data A : Set where
  a  : A
  eq : a ≡ a

ok : ∀ i → eq i ≡ a
ok i j = eq (primIMin i (primINeg j))

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ok #-}
