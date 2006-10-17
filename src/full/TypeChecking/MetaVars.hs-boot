
module TypeChecking.MetaVars where

import Syntax.Internal	       (MetaId, Args, Term, Sort)
import TypeChecking.Monad.Base (MetaInstantiation, TCM)

class HasMeta t where
    metaInstance :: t -> MetaInstantiation
    metaVariable :: MetaId -> Args -> t

instance HasMeta Term where
instance HasMeta Sort where

(=:) :: HasMeta t => MetaId -> t -> TCM ()

