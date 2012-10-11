module Agda.TypeChecking.Substitute where

import {-# SOURCE #-} Agda.Syntax.Internal (Term)
import Agda.Syntax.Position
import Agda.Utils.Size

data Substitution

instance KillRange Substitution
instance Sized     Substitution
instance Show      Substitution

idS :: Substitution

forceSubst :: Term -> Term

class Subst t where
  applySubst :: Substitution -> t -> t

instance Subst Term where
