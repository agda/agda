
module Agda.Syntax.Abstract.Pretty where

import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.TypeChecking.Monad
import Agda.Utils.Pretty

showA :: (Show c, ToConcrete a c, MonadAbsToCon m) => a -> m String
showA x = show <$> abstractToConcrete_ x

prettyA :: (Pretty c, ToConcrete a c, MonadAbsToCon m) => a -> m Doc
prettyA x = pretty <$> abstractToConcrete_ x

prettyAs :: (Pretty c, ToConcrete a [c], MonadAbsToCon m) => a -> m Doc
prettyAs x = fsep . map pretty <$> abstractToConcrete_ x

-- | Variant of 'showA' which does not insert outermost parentheses.

showATop :: (Show c, ToConcrete a c, MonadAbsToCon m) => a -> m String
showATop x = show <$> abstractToConcreteCtx TopCtx x

-- | Variant of 'prettyA' which does not insert outermost parentheses.

prettyATop :: (Pretty c, ToConcrete a c, MonadAbsToCon m) => a -> m Doc
prettyATop x = pretty <$> abstractToConcreteCtx TopCtx x
