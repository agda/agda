module Agda.TypeChecking.Primitive.Cubical.Base where

import Agda.TypeChecking.Monad.Pure
import Agda.Syntax.Internal

isCubicalSubtype :: PureTCM m => Type -> m (Maybe (Term, Term, Term, Term))
