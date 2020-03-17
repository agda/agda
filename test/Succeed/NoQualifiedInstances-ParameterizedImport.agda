{-# OPTIONS --no-qualified-instances #-}

module NoQualifiedInstances-ParameterizedImport where

postulate
  T : Set

open import NoQualifiedInstances.ParameterizedImport.A T as A

postulate
  f : {{A.I}} → A.I

test : A.I
test = f
