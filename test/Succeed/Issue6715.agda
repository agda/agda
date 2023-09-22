{-# OPTIONS --cubical #-}
module Issue6715 where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming (primTransp to transp; primIMin to _∧_; primINeg to ~_)

data U : Set where
  a : U
  squash : ∀ x y → x ≡ y

data IsA : U → Set where
  is-a : IsA a


t : {x : U} → IsA x → IsA x
t is-a = transp (λ i → IsA (squash a a i)) i0 is-a

lemma : {x : U} (p : IsA x) → PathP (λ i → IsA (squash x x i)) p (t p)
lemma is-a i = transp (λ j → IsA (squash a a (i ∧ j))) (~ i) is-a
