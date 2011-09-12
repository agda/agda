
module Agda.TypeChecking.Conversion where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareTerm :: MonadTCM tcm => Comparison -> Type -> Term -> Term -> tcm ()
compareAtom :: MonadTCM tcm => Comparison -> Type -> Term -> Term -> tcm ()
compareArgs :: MonadTCM tcm => [Polarity] -> Type -> Term -> Args -> Args -> tcm ()
compareElims :: MonadTCM tcm => [Polarity] -> Type -> Term -> [Elim] -> [Elim] -> tcm ()
compareType :: MonadTCM tcm => Comparison -> Type -> Type -> tcm ()
compareTel  :: MonadTCM tcm => Type -> Type -> Comparison -> Telescope -> Telescope -> tcm ()
compareSort :: MonadTCM tcm => Comparison -> Sort -> Sort -> tcm ()
equalTerm :: MonadTCM tcm => Type -> Term -> Term -> tcm ()
equalType :: MonadTCM tcm => Type -> Type -> tcm ()
equalSort :: MonadTCM tcm => Sort -> Sort -> tcm ()
leqType :: MonadTCM tcm => Type -> Type -> tcm ()
