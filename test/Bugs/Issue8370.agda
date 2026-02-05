{-# OPTIONS --cubical #-}
open import Agda.Primitive.Cubical renaming (primTransp to transp)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue
import Agda.Builtin.Equality as Id

data Canon : Set where
  canon : Canon

record R : Set₁ where
  constructor mkR
  pattern
  field
    getType : Set
into : {x y : Set} → x ≡ y → mkR x Id.≡ mkR y
into {x} p = transp (λ i → mkR x Id.≡ mkR (p i)) i0 Id.refl
back : {x y : R} → x Id.≡ y → R.getType x ≡ R.getType y
back {x} Id.refl i = R.getType x

hmm : transp (λ i → back (into (λ _ → Canon)) i) i0 canon ≡ canon
hmm i = canon
