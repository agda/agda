{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS.AsPatterns
  ( recoverAsPatterns ) where

import Control.Applicative
import Control.Monad.Writer hiding ((<>))
import qualified Data.Foldable as Fold

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Concrete ()
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

import Agda.Utils.Size
import Agda.Utils.Impossible
#include "undefined.h"

recoverAsPatterns :: Telescope -> Type -> Term -> [NamedArg A.Pattern] -> [NamedArg DeBruijnPattern] -> TCM [AsBinding]
recoverAsPatterns delta a self ps qs = do
  let es = patternsToElims qs
  as <- smashType (raise (size delta) a) self es
  ps <- insertImplicitPatternsT DontExpandLast ps a
  reportSDoc "tc.lhs.as" 30 $ vcat
    [ text "recovering as patterns"
    , nest 2 $ vcat [ text "es =" <+> prettyList (map prettyTCM es)
                    , text "as =" <+> prettyList (map prettyTCM as)
                    , text "ps =" <+> prettyList (map prettyA ps) ]
    ]
  execWriterT $ asPatterns as ps es

-- ProjT stores the type of the projected field.
data ElimType = ProjT Type | ArgT Type

instance PrettyTCM ElimType where
  prettyTCM (ProjT a) = text "." <> prettyTCM a
  prettyTCM (ArgT a)  = prettyTCM a

smashType :: Type -> Term -> Elims -> TCM [ElimType]
smashType a _ [] = return []
smashType a self (e : es) =
  case e of
    Apply v -> do
      Pi a b <- ignoreSharing <$> reduce (unEl a)
      (ArgT (unDom a) :) <$> smashType (absApp b $ unArg v) (self `applyE` [e]) es
    Proj f -> do
      a <- reduce a
      Just (_, self, a) <- projectTyped self a f
      (ProjT a :) <$> smashType a self es

smashTel :: Telescope -> [Term] -> [Type]
smashTel _ []                       = []
smashTel (ExtendTel a tel) (v : vs) = unDom a : smashTel (absApp tel v) vs
smashTel EmptyTel{} (_:_)           = __IMPOSSIBLE__

asPatterns :: [ElimType] -> [NamedArg A.Pattern] -> [Elim] -> WriterT [AsBinding] TCM ()
asPatterns _ [] _ = return ()
asPatterns (ProjT a : as) (p : ps) (Proj{} : vs) = do
  A.ProjP{} <- return $ namedArg p  -- sanity check
  ps <- lift $ insertImplicitPatternsT DontExpandLast ps a
  asPatterns as ps vs
asPatterns (ArgT a : as) (p : ps) (Apply v : vs)
  | noAsPatterns (namedArg p) = asPatterns as ps vs
  | otherwise =
    case namedArg p of
      A.AsP _ x p' -> do
        tell [AsB x (unArg v) a]
        asPatterns (ArgT a : as) (fmap (p' <$) p : ps) (Apply v : vs)
      A.ConP _ _ ps' -> do
        (_, _, tel, as', args) <- lift $ conPattern a (unArg v)
        ps' <- lift $ insertImplicitPatterns ExpandLast ps' tel
        asPatterns (map ArgT as' ++ as) (ps' ++ ps) (map Apply args ++ vs)
      A.RecP i fps -> do
        (r, c, _, as', args) <- lift $ conPattern a (unArg v)
        let fs  = zipWith (<$) (map (nameConcrete . qnameName) $ conFields c) args
        ps' <- lift $ insertMissingFields r (const $ A.WildP i) fps fs
        asPatterns (map ArgT as' ++ as) (ps' ++ ps) (map Apply args ++ vs)
      A.DefP{} -> __IMPOSSIBLE__ -- ?
      _ -> __IMPOSSIBLE__
asPatterns _ _ _ = __IMPOSSIBLE__

conPattern :: Type -> Term -> TCM (QName, ConHead, Telescope, [Type], Args)
conPattern a (Con c args) = do
  Just ca <- getConType c a
  TelV tel (El _ (Def d _)) <- telView ca
  let as = smashTel tel (map unArg args)
  return (d, c, tel, as, args)
conPattern _ _ = __IMPOSSIBLE__

noAsPatterns :: A.Pattern -> Bool
noAsPatterns p =
  case p of
    A.AsP{}         -> False
    A.ConP _ _ ps   -> noArgAsPats ps
    A.DefP _ _ ps   -> noArgAsPats ps
    A.RecP _ fs     -> all (Fold.all noAsPatterns) fs
    A.VarP{}        -> True
    A.ProjP{}       -> True
    A.WildP{}       -> True
    A.DotP{}        -> True
    A.AbsurdP{}     -> True
    A.LitP{}        -> True
    A.PatternSynP{} -> __IMPOSSIBLE__
  where
    noArgAsPats = all (noAsPatterns . namedArg)
