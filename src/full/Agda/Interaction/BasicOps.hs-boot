module Agda.Interaction.BasicOps where

import Agda.Syntax.Abstract (Expr)
import Agda.Syntax.Common (InteractionId)
import  {-# SOURCE #-} Agda.TypeChecking.Monad.Base (NamedMeta, TCWarning)

data OutputForm a b
data OutputConstraint a b
type Goals = ( [OutputConstraint Expr InteractionId] -- visible metas
             , [OutputConstraint Expr NamedMeta]     -- hidden metas
             )
type WarningsAndNonFatalErrors
      = ( [TCWarning] -- warnings
        , [TCWarning] -- non-fatal errors
        )
