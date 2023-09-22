module Issue6140 where

open import Agda.Builtin.List using (List)

import Issue6140.A

List-Functor = Issue6140.A.List-Functor

open import Common.Bool
open import Common.IO
open import Common.Unit

main : IO Unit
main = printBool true
