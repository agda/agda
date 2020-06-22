open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Common.IO

printTail : String → IO _
printTail str with primStringUncons str
... | just (_ , tl) = putStr tl
... | nothing       = putStr ""

main : _
main = printTail "/test/Compiler/simple/uncons.agda"
