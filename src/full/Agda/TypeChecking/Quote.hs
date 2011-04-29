
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

#include "../undefined.h"
import Agda.Utils.Impossible

quotingKit :: MonadTCM tcm => tcm ((Term -> Term), (Type -> Term))
quotingKit = do
  hidden <- primHidden
  visible <- primVisible
  relevant <- primRelevant
  irrelevant <- primIrrelevant
  forced <- primForced
  nil <- primNil
  cons <- primCons
  arg <- primArgArg
  var <- primAgdaTermVar
  lam <- primAgdaTermLam
  def <- primAgdaTermDef
  con <- primAgdaTermCon
  pi <- primAgdaTermPi
  sort <- primAgdaTermSort
  set <- primAgdaSortSet
  setLit <- primAgdaSortLit
  unsupportedSort <- primAgdaSortUnsupported
  sucLevel <- primLevelSuc
  lub <- primLevelMax
  el <- primAgdaTypeEl
  Con z _ <- primZero
  Con s _ <- primSuc
  unsupported <- primAgdaTermUnsupported
  let t @@ u = apply t [defaultArg u]
      quoteHiding Hidden    = hidden
      quoteHiding ImplicitFromScope = __IMPOSSIBLE__ -- quoting ImplicitFromScope args not yet supported...
      quoteHiding NotHidden = visible
      quoteRelevance Relevant   = relevant
      quoteRelevance Irrelevant = irrelevant
      quoteRelevance NonStrict  = __IMPOSSIBLE__ -- Andreas, 2011-04-29 TODO!!
      quoteRelevance Forced     = forced
      quoteLit (LitInt   _ n)   = iterate suc zero !! fromIntegral n
      quoteLit _                = unsupported
      -- We keep no ranges in the quoted term, so the equality on terms
      -- is only on the structure.
      quoteSortLevelTerm (Lit (LitLevel _ n)) = setLit @@ Lit (LitInt noRange n)
      quoteSortLevelTerm t                    = set @@ quote t
      quoteSort (Type t)    = quoteSortLevelTerm t
      quoteSort (Lub s1 s2) = lub @@ quoteSort s1 @@ quoteSort s2
      quoteSort (Suc s)     = sucLevel @@ quoteSort s
      quoteSort Prop        = unsupportedSort
      quoteSort MetaS{}     = unsupportedSort
      quoteSort Inf         = unsupportedSort
      quoteSort DLub{}      = unsupportedSort
      quoteType (El s t) = el @@ quoteSort s @@ quote t
      list [] = nil
      list (a : as) = cons @@ a @@ list as
      zero = con @@ quoteName z @@ nil
      suc n = con @@ quoteName s @@ list [n]
      quoteArg q (Arg h r t) = arg @@ quoteHiding h @@ quoteRelevance r @@ q t
      quoteArgs ts = list (map (quoteArg quote) ts)
      quote (Var n ts) = var @@ Lit (LitInt noRange n) @@ quoteArgs ts
      quote (Lam h t) = lam @@ quoteHiding h @@ quote (absBody t)
      quote (Def x ts) = def @@ quoteName x @@ quoteArgs ts
      quote (Con x ts) = con @@ quoteName x @@ quoteArgs ts
      quote (Pi t u) = pi @@ quoteArg quoteType t
                          @@ quoteType (absBody u)
      quote (Fun t u) = pi @@ quoteArg quoteType t
                           @@ quoteType (raise 1 u) -- do we want a raiseFrom here?
      quote (Lit lit) = quoteLit lit
      quote (Sort s)  = sort @@ quoteSort s
      quote MetaV{}   = unsupported
      quote DontCare  = unsupported -- could be exposed at some point but we have to take care
  return (quote, quoteType)

quoteName :: QName -> Term
quoteName x = Lit (LitQName noRange x)

quoteTerm :: MonadTCM tcm => Term -> tcm Term
quoteTerm v = ($v) . fst <$> quotingKit

quoteType :: MonadTCM tcm => Type -> tcm Term
quoteType v = ($v) . snd <$> quotingKit

agdaTermType :: MonadTCM tcm => tcm Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

qNameType :: MonadTCM tcm => tcm Type
qNameType = El (mkType 0) <$> primQName
