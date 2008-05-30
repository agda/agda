{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}
module Agda.Syntax.Abstract.Pretty where

import Control.Applicative

import Agda.Syntax.Abstract
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.TypeChecking.Monad
import Agda.Utils.Pretty

showA :: (Show c, ToConcrete a c, MonadTCM tcm) => a -> tcm String
showA x = show <$> abstractToConcrete_ x

prettyA :: (Pretty c, ToConcrete a c, MonadTCM tcm) => a -> tcm Doc
prettyA x = pretty <$> abstractToConcrete_ x

