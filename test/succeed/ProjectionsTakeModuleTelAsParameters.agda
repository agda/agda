-- Andreas, AIM XVIII, 2013-09-13
module ProjectionsTakeModuleTelAsParameters where

import Common.Level
open import Common.Equality

module M (A : Set) where

  record Prod (B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open Prod public

open M -- underapplied open

-- module parameters are hidden in projections

myfst : {A B : Set} → Prod A B → A
myfst = fst

mysnd : {A B : Set} → Prod A B → B
mysnd p = snd p

