module Agda.Interaction.BasicOps where

import Agda.Syntax.Abstract (Expr)
import Agda.Syntax.Common (InteractionId)
import  {-# SOURCE #-} Agda.TypeChecking.Monad.Base (NamedMeta, TCWarning)

data OutputForm a b
data OutputConstraint a b
data OutputConstraint' a b

data UseForce
instance Show UseForce
instance Read UseForce

data ComputeMode
instance Show ComputeMode
instance Read ComputeMode

data Rewrite
instance Show Rewrite
instance Read Rewrite

type Goals = ( [OutputConstraint Expr InteractionId] -- visible metas
             , [OutputConstraint Expr NamedMeta]     -- hidden metas
             )
type WarningsAndNonFatalErrors
      = ( [TCWarning] -- warnings
        , [TCWarning] -- non-fatal errors
        )
