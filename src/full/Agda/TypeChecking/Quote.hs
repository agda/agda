{-# LANGUAGE CPP, FlexibleInstances #-}

module Agda.TypeChecking.Quote where

import Control.Applicative

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal as I
import Agda.Syntax.Common

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute

#include "../undefined.h"
import Agda.Utils.Impossible

quotingKit :: TCM ((Term -> Term), (Type -> Term))
quotingKit = do
  hidden <- primHidden
  instanceH <- primInstance
  visible <- primVisible
  relevant <- primRelevant
  irrelevant <- primIrrelevant
  nil <- primNil
  cons <- primCons
  arg <- primArgArg
  arginfo <- primArgArgInfo
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
  Con z _ <- ignoreSharing <$> primZero
  Con s _ <- ignoreSharing <$> primSuc
  unsupported <- primAgdaTermUnsupported
  let t @@ u = apply t [defaultArg u]
      quoteHiding Hidden    = hidden
      quoteHiding Instance  = instanceH
      quoteHiding NotHidden = visible
      quoteRelevance Relevant   = relevant
      quoteRelevance Irrelevant = irrelevant
      quoteRelevance NonStrict  = relevant
      quoteRelevance Forced     = relevant
      quoteRelevance UnusedArg  = relevant
      quoteColors _ = nil -- TODO guilhem
      quoteArgInfo (ArgInfo h r cs) = arginfo @@ quoteHiding h
                                              @@ quoteRelevance r
                                --              @@ quoteColors cs
      quoteLit (LitInt   _ n)   = iterate suc zero !! fromIntegral n
      quoteLit _                = unsupported
      -- We keep no ranges in the quoted term, so the equality on terms
      -- is only on the structure.
      quoteSortLevelTerm (Max [])              = setLit @@ Lit (LitInt noRange 0)
      quoteSortLevelTerm (Max [ClosedLevel n]) = setLit @@ Lit (LitInt noRange n)
      quoteSortLevelTerm (Max [Plus 0 (NeutralLevel v)]) = set @@ quote v
      quoteSortLevelTerm _                     = unsupported
      quoteSort (Type t)    = quoteSortLevelTerm t
      quoteSort Prop        = unsupportedSort
      quoteSort Inf         = unsupportedSort
      quoteSort DLub{}      = unsupportedSort
      quoteType (El s t) = el @@ quoteSort s @@ quote t
      list [] = nil
      list (a : as) = cons @@ a @@ list as
      zero = con @@ quoteName z @@ nil
      suc n = con @@ quoteName s @@ list [arg @@ quoteArgInfo defaultArgInfo @@ n]
      quoteDom q (Dom info t) = arg @@ quoteArgInfo info @@ q t
      quoteArg q (Arg info t) = arg @@ quoteArgInfo info @@ q t
      quoteArgs ts = list (map (quoteArg quote) ts)
      quote (Var n ts) = var @@ Lit (LitInt noRange $ fromIntegral n) @@ quoteArgs ts
      quote (Lam info t) = lam @@ quoteHiding (getHiding info) @@ quote (absBody t)
      quote (Def x ts) = def @@ quoteName x @@ quoteArgs ts
      quote (Con x ts) = con @@ quoteName x @@ quoteArgs ts
      quote (Pi t u) = pi @@ quoteDom quoteType t
                          @@ quoteType (absBody u)
      quote (Level _) = unsupported
      quote (Lit lit) = quoteLit lit
      quote (Sort s)  = sort @@ quoteSort s
      quote (Shared p) = quote $ derefPtr p
      quote MetaV{}   = unsupported
      quote DontCare{} = unsupported -- could be exposed at some point but we have to take care
  return (quote, quoteType)

quoteName :: QName -> Term
quoteName x = Lit (LitQName noRange x)

quoteTerm :: Term -> TCM Term
quoteTerm v = ($v) . fst <$> quotingKit

quoteType :: Type -> TCM Term
quoteType v = ($v) . snd <$> quotingKit

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

qNameType :: TCM Type
qNameType = El (mkType 0) <$> primQName

isCon :: QName -> TCM Term -> TCM Bool
isCon con tm = do t <- tm
                  case ignoreSharing t of
                    Con con' _ -> return (con == con')
                    _ -> return False

unquoteFailedGeneric :: String -> TCM a
unquoteFailedGeneric msg = typeError . GenericError $ "Unable to unquote the " ++ msg

unquoteFailed :: String -> String -> Term -> TCM a
unquoteFailed kind msg t = do doc <- prettyTCM t
                              unquoteFailedGeneric $ "term (" ++ show doc ++ ") of type " ++ kind ++ ".\nReason: " ++ msg ++ "."

class Unquote a where
  unquote :: Term -> TCM a

unquoteH :: Unquote a => I.Arg Term -> TCM a
unquoteH a | isHidden a && isRelevant a =
    unquote $ unArg a
unquoteH _ = unquoteFailedGeneric "argument. It should be `hidden'."

unquoteN :: Unquote a => I.Arg Term -> TCM a
unquoteN a | notHidden a && isRelevant a =
    unquote $ unArg a
unquoteN _ = unquoteFailedGeneric "argument. It should be `visible'"

choice :: Monad m => [(m Bool, m a)] -> m a -> m a
choice [] dflt = dflt
choice ((mb, mx) : mxs) dflt = do b <- mb
                                  if b then mx else choice mxs dflt

instance Unquote I.ArgInfo where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [h,r] -> do
        choice
          [(c `isCon` primArgArgInfo, ArgInfo <$> unquoteN h <*> unquoteN r <*> return [])]
          (unquoteFailed "ArgInfo" "arity 2 and not the `arginfo' constructor" t)
      _ -> unquoteFailed "ArgInfo" "not of arity 2" t

instance Unquote a => Unquote (I.Arg a) where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [info,x] -> do
        choice
          [(c `isCon` primArgArg, Arg <$> unquoteN info <*> unquoteN x)]
          (unquoteFailed "Arg" "arity 2 and not the `arg' constructor" t)
      _ -> unquoteFailed "Arg" "not of arity 2" t

instance Unquote Integer where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitInt _ n) -> return n
      _ -> unquoteFailed "Integer" "not a literal integer" t

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [x,xs] -> do
        choice
          [(c `isCon` primCons, (:) <$> unquoteN x <*> unquoteN xs)]
          (unquoteFailed "List" "arity 2 and not the `∷' constructor" t)
      Con c [] -> do
        choice
          [(c `isCon` primNil, return [])]
          (unquoteFailed "List" "arity 0 and not the `[]' constructor" t)
      _ -> unquoteFailed "List" "neither `[]' nor `∷'" t

instance Unquote Hiding where
  unquote t = do
    t <- reduce t
    let err = unquoteFailed "Hiding" "neither `hidden' nor `visible'" t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primHidden,  return Hidden)
          ,(c `isCon` primInstance, return Instance)
          ,(c `isCon` primVisible, return NotHidden)]
          err
      Con c vs -> unquoteFailed "Hiding" "the value is a constructor, but its arity is not 0" t
      _        -> err

instance Unquote Relevance where
  unquote t = do
    t <- reduce t
    let err = unquoteFailed "Relevance" "neither `relevant' or `irrelevant'" t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primRelevant,   return Relevant)
          ,(c `isCon` primIrrelevant, return Irrelevant)]
          err
      Con c vs -> unquoteFailed "Relevance" "the value is a constructor, but its arity is not 0" t
      _        -> err

instance Unquote QName where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Lit (LitQName _ x) -> return x
      _                  -> unquoteFailed "QName" "not a literal qname value" t

instance Unquote a => Unquote (Abs a) where
  unquote t = do x <- freshNoName_
                 Abs (show x) <$> unquote t

instance Unquote Sort where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primAgdaSortUnsupported, unquoteFailed "Sort" "unsupported sort" t)]
          (unquoteFailed "Sort" "arity 0 and not the `unsupported' constructor" t)
      Con c [u] -> do
        choice
          [(c `isCon` primAgdaSortSet, Type <$> unquoteN u)
          ,(c `isCon` primAgdaSortLit, Type . levelMax . (:[]) . ClosedLevel <$> unquoteN u)]
          (unquoteFailed "Sort" "arity 1 and not the `set' or the `lit' constructors" t)
      _ -> unquoteFailed "Sort" "not of arity 0 nor 1" t

instance Unquote Level where
  unquote l = Max . (:[]) . Plus 0 . UnreducedLevel <$> unquote l

instance Unquote Type where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [s, u] -> do
        choice
          [(c `isCon` primAgdaTypeEl, El <$> unquoteN s <*> unquoteN u)]
          (unquoteFailed "Type" "arity 2 and not the `el' constructor" t)
      _ -> unquoteFailed "Type" "not of arity 2" t

instance Unquote Term where
  unquote t = do
    t <- reduce t
    case ignoreSharing t of
      Con c [] ->
        choice
          [(c `isCon` primAgdaTermUnsupported, unquoteFailed "Term" "unsupported term" t)]
          (unquoteFailed "Term" "arity 0 and not the `unsupported' constructor" t)

      Con c [x] -> do
        choice
          [(c `isCon` primAgdaTermSort, Sort <$> unquoteN x)]
          (unquoteFailed "Term" "arity 1 and not the `sort' constructor" t)

      Con c [x,y] ->
        choice
          [(c `isCon` primAgdaTermVar, Var <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          ,(c `isCon` primAgdaTermCon, Con <$> unquoteN x <*> unquoteN y)
          ,(c `isCon` primAgdaTermDef, Def <$> unquoteN x <*> unquoteN y)
          ,(c `isCon` primAgdaTermLam, Lam <$> (flip setHiding defaultArgInfo <$> unquoteN x) <*> unquoteN y)
          ,(c `isCon` primAgdaTermPi,  Pi  <$> (domFromArg <$> unquoteN x) <*> unquoteN y)]
          (unquoteFailed "Term" "arity 2 and none of Var, Con, Def, Lam, Pi" t)

      Con{} -> unquoteFailed "Term" "neither arity 0 nor 1 nor 2" t
      Lit{} -> unquoteFailed "Term" "unexpected literal" t
      _ -> unquoteFailed "Term" "not a constructor" t
