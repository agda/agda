
module Agda.TypeChecking.Quote where

import Control.Applicative

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty

quoteTerm :: Term -> TCM Term
quoteTerm v = Lit . LitString noRange . show <$> prettyTCM v

quoteType :: Type -> TCM Term
quoteType t = Lit . LitString noRange . show <$> prettyTCM t

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primString

