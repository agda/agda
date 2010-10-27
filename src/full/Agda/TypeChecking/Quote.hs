
module Agda.TypeChecking.Quote where

import Control.Applicative

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute

quoteTerm :: Term -> TCM Term
quoteTerm v = do
  false <- primFalse
  true <- primTrue
  nil <- primNil
  cons <- primCons
  arg <- primArgArg
  var <- primAgdaTermVar
  lam <- primAgdaTermLam
  def <- primAgdaTermDef
  con <- primAgdaTermCon
  pi <- primAgdaTermPi
  sort <- primAgdaTermSort
  Con z _ <- primZero
  Con s _ <- primSuc
  unsupported <- primAgdaTermUnsupported
  let t @@ u = apply t [defaultArg u]
      quoteHiding Hidden = true
      quoteHiding NotHidden = false
      list [] = nil
      list (a : as) = cons @@ a @@ list as
      zero = con @@ quoteName z @@ nil
      suc n = con @@ quoteName s @@ list [n]
      quoteArg (Arg h r t) = arg @@ quoteHiding h @@ quote t
      quoteArgs ts = list (map quoteArg ts)
      quote (Var n ts) = var @@ Lit (LitInt noRange n) @@ quoteArgs ts
      quote (Lam h t) = lam @@ quoteHiding h @@ quote (absBody t)
      quote (Def x ts) = def @@ quoteName x @@ quoteArgs ts
      quote (Con x ts) = con @@ quoteName x @@ quoteArgs ts
      quote (Pi t u) = pi @@ quoteArg (fmap unEl t)
                          @@ quote (unEl (absBody u))
      quote (Fun t u) = pi @@ quoteArg (fmap unEl t)
                           @@ quote (raise 1 (unEl u))
      quote (Lit (LitInt _ n)) = iterate suc zero !! fromIntegral n
      quote (Sort _) = sort
      quote _ = unsupported
  return (quote v)

quoteName :: QName -> Term
quoteName x = Lit (LitQName noRange x)

quoteType :: Type -> TCM Term
quoteType (El _ v) = quoteTerm v

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

qNameType :: TCM Type
qNameType = El (mkType 0) <$> primQName
