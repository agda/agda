{-# OPTIONS -fglasgow-exts -cpp #-}

{-| Translate Agda names into a variety of GHC names
-}

module Agda.Compiler.Agate.TranslateName where

#include "../../undefined.h"
import Agda.Utils.Impossible

import Data.Char

----------------------------------------------------------------

translateNameAsUntypedTerm :: String -> String
translateNameAsUntypedTerm "_"                 = "_"
translateNameAsUntypedTerm s   | all isDigit s = 'x':s
translateNameAsUntypedTerm s                   = 'x':'_':escape s

translateNameAsUntypedConstructor :: String -> String
translateNameAsUntypedConstructor s = 'C':'_':escape s

translateNameAsOptimizedType :: String -> String
translateNameAsOptimizedType "_" = "_"
translateNameAsOptimizedType s   = 'T':'_':escape s

translateNameAsOptimizedTerm :: String -> String
translateNameAsOptimizedTerm "_"                 = "_"
translateNameAsOptimizedTerm s   | all isDigit s = 'o':s
translateNameAsOptimizedTerm s                   = 'o':'_':escape s

translateNameAsOptimizedConstructor :: String -> String
translateNameAsOptimizedConstructor s = 'D':'_':escape s

----------------------------------------------------------------

escape :: String -> String
escape ""      = ""
escape "_"     = "_"
escape (c:s) | isUpper c || isLower c || isDigit c = c:escape s
escape ('.':s) = '_':'_':escape s
escape ('_':s) = '_':'z':escape s
escape (c:s) | ord c >= 256
	       = '_':'u'
                    :intToDigit (ord c `div` 4096)
                    :intToDigit ((ord c `div` 256) `mod` 16)
                    :intToDigit ((ord c `div` 16)  `mod` 16)
                    :intToDigit (ord c `mod` 16):escape s
escape (c:s)   = '_':intToDigit (ord c `div` 16)
                    :intToDigit (ord c `mod` 16):escape s

----------------------------------------------------------------
                    
