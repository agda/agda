
module _ where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

data D (A : Set) : Set where
  L : A → D A
  R : A → D A

data T : Set where
  Var : (s : D String) → T

test : T → String
test (Var (L "abc")) = ""
test (Var (L s)) = ""
test (Var (R s)) = ""
