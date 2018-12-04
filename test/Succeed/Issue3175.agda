open import Data.List using (List; []; _∷_; map; foldr; _++_)

data Rose (A : Set) : Set where
  leaf : (a : A) → Rose A
  node : (rs : List (Rose A)) → Rose A

record IsSeq (A S : Set) : Set where
  field
    nil : S
    sg  : (a : A) → S
    _∙_ : (s t : S) → S

  concat : (ss : List S) → S
  concat = foldr _∙_ nil

open IsSeq {{...}}

{-# TERMINATING #-}
flatten : ∀{A S} {{_ : IsSeq A S}} → Rose A → S
flatten (leaf a) = sg a
flatten (node rs) = concat (map flatten rs)
