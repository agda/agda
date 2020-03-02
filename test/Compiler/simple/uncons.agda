open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Common.IO

printTail : String → IO _
printTail str with primStringUncons str
... | just (_ , tl) = putStr tl
... | nothing       = putStr ""


postulate
  readFile : String → IO String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC readFile = \ fp -> T.pack <$> readFile (T.unpack fp) #-}

main : _
main = readFile "test/Compiler/simple/uncons.agda" >>= printTail
