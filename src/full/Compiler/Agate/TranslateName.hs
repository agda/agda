{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| Translate Agda names into a variety of GHC names
-}

module Compiler.Agate.TranslateName where

import Char(isDigit,intToDigit,isAlpha,isLower,isUpper,ord)
import GHC.Base (map)

import Syntax.Internal
import Syntax.Scope
import Syntax.Common

----------------------------------------------------------------

translateNameAsUntypedTerm :: Show a => a -> String
translateNameAsUntypedTerm s = 'x':'_':escape (show s)

translateNameAsUntypedConstructor :: Show a => a -> String
translateNameAsUntypedConstructor s = 'C':'_':escape (show s)

translateNameAsOptimizedType :: Show a => a -> String
translateNameAsOptimizedType s = 'T':'_':escape (show s)

translateNameAsOptimizedTerm :: Show a => a -> String
translateNameAsOptimizedTerm s = 'o':'_':escape (show s)

translateNameAsOptimizedConstructor :: Show a => a -> String
translateNameAsOptimizedConstructor s = 'D':'_':escape (show s)

----------------------------------------------------------------

escape :: String -> String
escape [] = []
escape (c:s) | isUpper c || isLower c || isDigit c = c:escape s
escape ('_':s) = '_':'_':escape s
escape (c:s)   | ord c >= 256
	       = '_':'u'
                    :intToDigit (ord c `div` 4096)
                    :intToDigit ((ord c `div` 256) `mod` 16)
                    :intToDigit ((ord c `div` 16)  `mod` 16)
                    :intToDigit (ord c `mod` 16):escape s
escape (c:s)   = '_':intToDigit (ord c `div` 16)
                    :intToDigit (ord c `mod` 16):escape s

----------------------------------------------------------------
                    