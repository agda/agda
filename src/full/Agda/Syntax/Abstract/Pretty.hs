{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Abstract.Pretty where

import Agda.Syntax.Fixity
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Common.Pretty

showA :: (ToConcrete a, Show (ConOfAbs a), MonadAbsToCon m) => a -> m String
showA x = show <$> abstractToConcrete_ x

prettyA :: (ToConcrete a, Pretty (ConOfAbs a), MonadAbsToCon m) => a -> m Doc
prettyA x = pretty <$> abstractToConcrete_ x

prettyAs :: (ToConcrete a, ConOfAbs a ~ [ce], Pretty ce, MonadAbsToCon m) => a -> m Doc
prettyAs x = fsep . map pretty <$> abstractToConcrete_ x

-- | Variant of 'showA' which does not insert outermost parentheses.

showATop :: (ToConcrete a, Show (ConOfAbs a), MonadAbsToCon m) => a -> m String
showATop x = show <$> abstractToConcreteCtx TopCtx x

-- | Variant of 'prettyA' which does not insert outermost parentheses.

prettyATop :: (ToConcrete a, Pretty (ConOfAbs a),  MonadAbsToCon m) => a -> m Doc
prettyATop x = pretty <$> abstractToConcreteCtx TopCtx x
