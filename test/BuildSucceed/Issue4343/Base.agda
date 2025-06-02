module Base where

open import Agda.Builtin.Bool             public
open import Agda.Builtin.Equality         public
open import Agda.Builtin.Equality.Rewrite public

postulate
  a b c d e : Bool

f : Bool → Bool
f true  = e
f false = e
