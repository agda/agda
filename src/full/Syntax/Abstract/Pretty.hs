{-# OPTIONS -fglasgow-exts #-}
module Syntax.Abstract.Pretty where

import Syntax.Translation.AbstractToConcrete

showA :: (Show c, ToConcrete a c) => a -> String
showA = show . abstractToConcrete_

