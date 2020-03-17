module NoQualifiedInstances.ParameterizedImport.A (T : Set) where

record I : Set where

postulate instance i : I
