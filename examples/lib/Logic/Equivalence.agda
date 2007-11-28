
module Logic.Equivalence where

import Logic.Relations
open   Logic.Relations

record Equivalence (A : Set) : Set1 where
  field
    _==_  : Rel A
    refl  : Reflexive _==_
    sym   : Symmetric _==_
    trans : Transitive _==_

