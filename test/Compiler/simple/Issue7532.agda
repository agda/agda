
module Issue7532 where

open import Common.IO

open import Agda.Builtin.String

go : (F : Set → Set)(f : Set → String) → String
go F f = f (F String)

hello : String
hello = go (λ A → A) (λ A → "hello world")

main = putStr hello
