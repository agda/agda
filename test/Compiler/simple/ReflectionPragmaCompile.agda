module _ where

import Agda.Builtin.Reflection.External
open import Common.IO hiding (_>>=_)
open import Common.List using ([])
open import Common.Reflection
open import Common.Unit using (Unit)

infixr 0 _$_
_$_ : {A B : Set} → (A → B) → A → B
_$_ f = f

id-type : Type
id-type = pi (hArg $ sort $ lit 0) $
    abs "A" $ pi (vArg $ var 0 []) $
    abs "x" $ var 1 []

unquoteDecl id = do
    _ ← declarePostulate (vArg id) id-type
    _ ← pragmaCompile "GHC" id "= \\ _ x -> x"
    pragmaCompile "JS" id "= (a) => (x) => x"

main : IO Unit
main = putStrLn (id "Hello world")
