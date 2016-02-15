-- ASR (2016-02-15). In the Makefile in test/compiler founded in the
-- 2.4.2.3 tag, this test used the options `+RTS -H1G -M1.5G -RTS`.

module AllStdLib where

-- Ensure that the entire standard library is compiled.
import README

open import Data.Unit.Base
open import Data.String
open import IO
import IO.Primitive as Prim

main : Prim.IO ⊤
main = run (putStrLn "Hello World!")
