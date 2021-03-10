{-# OPTIONS --no-qualified-instances #-}

module NoQualifiedInstances-Import where

open import NoQualifiedInstances.Import.A as A

postulate
  f : {{A.I}} → A.I

test : A.I
test = f
