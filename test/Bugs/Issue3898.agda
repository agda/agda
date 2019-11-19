{-# OPTIONS -v tc.force:60 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.List

module _ {a} {A : Set a} where

  [_] : A → List A
  [ x ] = x ∷ []

  data FSet : List A → Set a where
    sg  : (x : A) → FSet [ x ]
        -- ^ should be forced

  HOLE : Set
  HOLE = {!!}  -- just to force make bugs to look at the output
