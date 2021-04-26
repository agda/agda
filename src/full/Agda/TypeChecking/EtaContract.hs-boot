
module Agda.TypeChecking.EtaContract where

import Agda.Syntax.Internal (Term)
import Agda.TypeChecking.Monad.Base (TCM)

etaContractTCM :: Term -> TCM Term
