{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.Erase (eraseTerms) where

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

eraseTerms :: TTerm -> TCM TTerm
eraseTerms = runE . erase
  where
    erase t = case tAppView t of

      TCon c : vs -> do
        (rs, _) <- getFunInfo c
        when (length rs < length vs) __IMPOSSIBLE__
        TApp (TCon c) <$> zipWithM eraseRel rs vs

      TDef f : vs -> do
        (rs, h) <- getFunInfo f
        let fullyApplied = length rs == length vs
            dontErase    = TApp (TDef f) <$> zipWithM eraseRel (rs ++ repeat Relevant) vs
        case h of
          Erasable | fullyApplied -> pure TErased   -- TODO: can we erase underapplied things?
          _ -> dontErase

      _ -> case t of
        TVar{}         -> pure t
        TDef{}         -> pure t
        TPrim{}        -> pure t
        TLit{}         -> pure t
        TCon{}         -> pure t
        TApp f es      -> TApp <$> erase f <*> mapM erase es
        TLam b         -> TLam <$> erase b
        TLet e b       -> TLet <$> erase e <*> erase b
        TCase x t d bs -> TCase x t <$> erase d <*> mapM eraseAlt bs

        TPi a b        -> pure TErased
        TUnit          -> pure t
        TSort          -> pure t
        TErased        -> pure t
        TError{}       -> pure t

    eraseRel r t | erasableR r = pure TErased
                 | otherwise   = erase t

    eraseAlt a = case a of
      TALit l b   -> TALit l   <$> erase b
      TACon c a b -> TACon c a <$> erase b
      TAPlus k b  -> TAPlus k  <$> erase b

data TypeInfo = Erasable | NotErasable
  deriving (Eq, Show)

erasableR :: Relevance -> Bool
erasableR Relevant   = False
erasableR Forced{}   = False    -- TODO: should be True but need to transform clauses
erasableR NonStrict  = True
erasableR Irrelevant = True
erasableR UnusedArg  = True

erasable :: TypeInfo -> Bool
erasable Erasable    = True
erasable NotErasable = False

type FunInfo = ([Relevance], TypeInfo)

getFunInfo :: QName -> E FunInfo
getFunInfo q = memo (funMap . key q) $ getInfo q
  where
    getInfo q = do
      (rs, t) <- lift $ do
        (tel, t) <- typeWithoutParams q
        return (map getRelevance tel, t)
      h <- getTypeInfo t
      lift $ reportSLn "treeless.opt.erase.info" 50 $ "type info for " ++ show q ++ ": " ++ show rs ++ " -> " ++ show h
      return (rs, h)

typeWithoutParams :: QName -> TCM (ListTel, Type)
typeWithoutParams q = do
  def <- getConstInfo q
  let d = case I.theDef def of
        Function{ funProjection = Just Projection{ projIndex = i } } -> i - 1
        Constructor{ conPars = n } -> n
        _                          -> 0
  TelV tel t <- telView (defType def)
  return (drop d $ telToList tel, t)

getTypeInfo :: Type -> E TypeInfo
getTypeInfo t = do
  t <- lift $ reduce t
  e <- case ignoreSharing $ I.unEl t of
    I.Def d _ -> typeInfo d
    Sort{}    -> return Erasable
    _         -> return NotErasable
  lift $ reportSDoc "treeless.opt.erase.type" 50 $ prettyTCM t <+> text ("is " ++ show e)
  return e
  where
    typeInfo :: QName -> E TypeInfo
    typeInfo q = memo (typeMap . key q) $ do
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
        Just [] -> return Erasable
        _       -> return NotErasable

