
module Issue7532-obfuscated where

open import Common.IO

open import Agda.Builtin.String

go : (F : Set → Set)(f : Set → String) → String
go F f = f (F String)

Id : Set → Set
Id A = A

hello : String
hello = go Id (λ A → "hello world")

main = putStr hello
