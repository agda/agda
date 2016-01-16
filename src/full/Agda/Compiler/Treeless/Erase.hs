{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

module Agda.Compiler.Treeless.Erase (eraseTerms) where

import Control.Arrow ((&&&), (***), first, second)
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad as I
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Pretty

import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Pretty

import Agda.Utils.Maybe
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Memo

#include "undefined.h"

data ESt = ESt { _funMap  :: Map QName FunInfo
               , _typeMap :: Map QName TypeInfo }

funMap :: Lens' (Map QName FunInfo) ESt
funMap f r = f (_funMap r) <&> \ a -> r { _funMap = a }

typeMap :: Lens' (Map QName TypeInfo) ESt
typeMap f r = f (_typeMap r) <&> \ a -> r { _typeMap = a }

type E = StateT ESt TCM

runE :: E a -> TCM a
runE m = evalStateT m (ESt Map.empty Map.empty)

eraseTerms :: QName -> TTerm -> TCM TTerm
eraseTerms q = runE . eraseTop q
  where
    eraseTop q t = do
      (_, h) <- getFunInfo q
      case h of
        Erasable -> pure TErased
        Empty    -> pure TErased
        _        -> erase t

    erase t = case tAppView t of

      TCon c : vs -> do
        (rs, h) <- getFunInfo c
        when (length rs < length vs) __IMPOSSIBLE__
        case h of
          Erasable -> pure TErased
          Empty    -> pure TErased
          _        -> tApp (TCon c) <$> zipWithM eraseRel rs vs

      TDef f : vs -> do
        (rs, h) <- getFunInfo f
        case h of
          Erasable -> pure TErased
          Empty    -> pure TErased
          _        -> tApp (TDef f) <$> zipWithM eraseRel (rs ++ repeat Relevant) vs

      _ -> case t of
        TVar{}         -> pure t
        TDef{}         -> pure t
        TPrim{}        -> pure t
        TLit{}         -> pure t
        TCon{}         -> pure t
        TApp f es      -> tApp <$> erase f <*> mapM erase es
        TLam b         -> tLam <$> erase b
        TLet e b       -> do
          e <- erase e
          if isErased e
            then case b of
                   TCase 0 _ _ _ -> tLet TErased <$> erase b
                   _             -> erase $ subst 0 TErased b else do
            tLet e <$> erase b
        TCase x t d bs -> do
          d  <- erase d
          bs <- mapM eraseAlt bs
          tCase x t d bs

        TUnit          -> pure t
        TSort          -> pure t
        TErased        -> pure t
        TError{}       -> pure t

    tLam TErased = TErased
    tLam t       = TLam t

    tLet e b
      | freeIn 0 b = TLet e b
      | otherwise  = strengthen __IMPOSSIBLE__ b

    tApp f []                  = f
    tApp TErased _             = TErased
    tApp f _ | isUnreachable f = tUnreachable
    tApp f es                  = TApp f es

    tCase x t d bs
      | isErased d && all (isErased . aBody) bs = pure TErased
      | otherwise = case bs of
        [TACon c a b] -> do
          h <- snd <$> getFunInfo c
          case h of
            NotErasable -> noerase
            Empty       -> pure TErased
            Erasable    -> (if a == 0 then pure else erase) $ applySubst (replicate a TErased ++# idS) b
                              -- might enable more erasure
        _ -> noerase
      where
        noerase = pure $ TCase x t d bs

    isErased t = t == TErased || isUnreachable t

    eraseRel r t | erasableR r = pure TErased
                 | otherwise   = erase t

    eraseAlt a = case a of
      TALit l b   -> TALit l   <$> erase b
      TACon c a b -> TACon c a <$> erase b
      TAGuard g b -> TAGuard   <$> erase g <*> erase b

data TypeInfo = Empty | Erasable | NotErasable
  deriving (Eq, Show)

erasableR :: Relevance -> Bool
erasableR Relevant   = False
erasableR Forced{}   = False    -- TODO: should be True but need to transform clauses
erasableR NonStrict  = True
erasableR Irrelevant = True
erasableR UnusedArg  = True

erasable :: TypeInfo -> Bool
erasable Erasable    = True
erasable Empty       = True
erasable NotErasable = False

type FunInfo = ([Relevance], TypeInfo)

getFunInfo :: QName -> E FunInfo
getFunInfo q = memo (funMap . key q) $ getInfo q
  where
    getInfo q = do
      (rs, t) <- lift $ do
        (tel, t) <- typeWithoutParams q
        return (map getRelevance tel, t)
      h <- if isAbsurdLambdaName q then pure Erasable else getTypeInfo t
      lift $ reportSLn "treeless.opt.erase.info" 50 $ "type info for " ++ show q ++ ": " ++ show rs ++ " -> " ++ show h
      return (rs, h)

telListView :: Type -> TCM (ListTel, Type)
telListView t = do
  TelV tel t <- telView t
  return (telToList tel, t)

typeWithoutParams :: QName -> TCM (ListTel, Type)
typeWithoutParams q = do
  def <- getConstInfo q
  let d = case I.theDef def of
        Function{ funProjection = Just Projection{ projIndex = i } } -> i - 1
        Constructor{ conPars = n } -> n
        _                          -> 0
  first (drop d) <$> telListView (defType def)

getTypeInfo :: Type -> E TypeInfo
getTypeInfo t = do
  (tel, t) <- lift $ telListView t
  et <- case ignoreSharing $ I.unEl t of
    I.Def d _ -> typeInfo d
    Sort{}    -> return Erasable
    _         -> return NotErasable
  is <- mapM (getTypeInfo . snd . dget) tel
  let e | et == Empty       = Empty
        | any (== Empty) is = Erasable
        | otherwise         = et
  lift $ reportSDoc "treeless.opt.erase.type" 50 $ prettyTCM t <+> text ("is " ++ show e)
  return e
  where
    typeInfo :: QName -> E TypeInfo
    typeInfo q = memoRec (typeMap . key q) Erasable $ do  -- assume recursive occurrences are erasable
      def <- lift $ getConstInfo q
      mcs <- return $ case I.theDef def of
        I.Datatype{ dataCons = cs } -> Just cs
        I.Record{ recConHead = c }  -> Just [conName c]
        _                           -> Nothing
      case mcs of
        Just [c] -> do
          (ts, _) <- lift $ typeWithoutParams c
          let rs = map getRelevance ts
          is <- mapM (getTypeInfo . snd . dget) ts
          let er = and [ erasable i || erasableR r | (i, r) <- zip is rs ]
          return $ if er then Erasable else NotErasable
        Just [] -> return Empty
        _       -> return NotErasable

