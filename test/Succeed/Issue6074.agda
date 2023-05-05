{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Issue6074 where

open import Agda.Primitive.Cubical

-- Issue 6074: If @funSort IUniv ? = Set _@ then @? = Set _@
-- Previously would complain IUniv ≠ Set _
_ : Set
_ = I → {!   !}
