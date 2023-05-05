-- original test case by Jesper Cockx
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool

macro
  getMeta : Term → TC ⊤
  getMeta hole@(meta m _) = quoteTC m >>= unify hole
  getMeta _ = typeError []

myMeta : Meta
myMeta = getMeta

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}
{-# COMPILE JS  putStrLn = function(x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (append (primShowMeta myMeta ∷
                         showBool (primMetaEquality myMeta myMeta) ∷
                         showBool (primMetaLess myMeta myMeta) ∷ []))
  where
    nl : String → String
    nl s = primStringAppend s "\n"
    append : List String → String
    append [] = ""
    append (x ∷ xs) = primStringAppend (nl x) (append xs)
    showBool : Bool → String
    showBool false = "false"
    showBool true = "true"
