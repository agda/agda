module Agda.TypeChecking.Eliminators where

import Agda.Syntax.Common (Nat)
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

-- | Weak head normal form in elimination presentation.
data ElimView
  = VarElim  Nat    [Elim]   -- ^ Neutral term @x es@.
  | DefElim  QName  [Elim]   -- ^ Irreducible function application @f es@.
  | ConElim  ConHead Args    -- ^ Only 'Apply' eliminations @c vs@.
  | MetaElim MetaId [Elim]   -- ^ Stuck on meta variable @X es@.
  | NoElim   Term

elimView :: (MonadReduce m, MonadTCEnv m, HasConstInfo m) => Bool -> Term -> m Term

unElim :: Term -> [Elim] -> Term
