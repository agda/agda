
-- Code demonstrating erasure bug in JS backend,
-- resistant to naive patches of Agda's earser (e.g. #7597)

module Issue7532-obfuscated-ghc where

open import Common.IO

open import Agda.Builtin.String

go : (F : Set → Set)(f : Set → String) → String
go F f = f (F String)

Id : Set → Set
Id A = A

hello : String
hello = go Id (λ A → "hello world")

main = putStr hello
