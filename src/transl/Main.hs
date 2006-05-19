{- Translator from Agda to Agda 2 -}

module Main where

-- Agda 1
import CParser
import Lex
import CSyntax

-- Agda 2
import Syntax.Concrete
import Syntax.Concrete.Pretty

main = putStrLn "Foo"

