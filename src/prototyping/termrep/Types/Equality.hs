
module Types.Equality where

import Types.Monad

eqType :: TermRep r => Type r -> Type r -> TC r (Constraints r)
eqType a b = error "todo: eqType"

