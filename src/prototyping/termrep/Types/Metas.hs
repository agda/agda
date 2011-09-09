
module Types.Metas where

import Types.Monad

blockTerm :: TermRep r => Term r -> Type r -> TC r (Constraints r) -> TC r (Term r)
blockTerm v a check = error "todo: blockTerm"

