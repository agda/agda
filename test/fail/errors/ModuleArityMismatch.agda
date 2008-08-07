module ModuleArityMismatch where

 module M (A : Set) where

 postulate
   A : Set

 module M′ = M A A
