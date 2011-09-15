
module Agda.Syntax.Abstract.Pretty where

import Control.Applicative

import Agda.Syntax.Abstract
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.TypeChecking.Monad
import Agda.Utils.Pretty

showA :: (Show c, ToConcrete a c) => a -> TCM String
showA x = show <$> abstractToConcrete_ x

prettyA :: (Pretty c, ToConcrete a c) => a -> TCM Doc
prettyA x = pretty <$> abstractToConcrete_ x

-- | Variant of 'showA' which does not insert outermost parentheses.

showATop :: (Show c, ToConcrete a c) => a -> TCM String
showATop x = show <$> abstractToConcreteCtx TopCtx x

-- | Variant of 'prettyA' which does not insert outermost parentheses.

prettyATop :: (Pretty c, ToConcrete a c) => a -> TCM Doc
prettyATop x = pretty <$> abstractToConcreteCtx TopCtx x
