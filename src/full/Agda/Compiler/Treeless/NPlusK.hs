{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.NPlusK
  ( introduceNPlusK ) where

import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Maybe
import Agda.Utils.Impossible

#include "undefined.h"

natKit :: TCM (Maybe (QName, QName))
natKit = do
    I.Con zero _ <- primZero
    I.Con suc  _ <- primSuc
    return $ Just (I.conName zero, I.conName suc)
  `catchError` \_ -> return Nothing

introduceNPlusK :: TTerm -> TCM TTerm
introduceNPlusK t =
  caseMaybeM natKit (return t) $ \(zero, suc) ->
    return $ transform (== zero) (== suc) t

transform :: (QName -> Bool) -> (QName -> Bool) -> TTerm -> TTerm
transform isZero isSuc = tr
  where
    tr t = case t of

      TCon c | isZero c -> TLit (LitInt noRange 0)
             | isSuc c  -> TLam (TPlus 1 (TVar 0))
      TApp (TCon s) [e] | isSuc s ->
        case tr e of
          TLit (LitInt r n) -> TLit (LitInt r (n + 1))
          TPlus i e         -> TPlus (i + 1) e
          e                 -> TPlus 1 e

      TCase e t d bs -> TCase e t (tr d) $ concatMap trAlt bs
        where
          trAlt b = case b of
            TACon c 0 b | isZero c -> [TALit (LitInt noRange 0) (tr b)]
            TACon c 1 b | isSuc c  -> [TAPlus 1 (tr b)]
              -- TODO: fuse cascading matches

            TACon c a b -> [TACon c a (tr b)]
            TALit{}     -> [b]
            TAPlus{}    -> __IMPOSSIBLE__

      TVar{}    -> t
      TDef{}    -> t
      TCon{}    -> t
      TLit{}    -> t
      TUnit{}   -> t
      TSort{}   -> t
      TErased{} -> t
      TError{}  -> t

      TPi (TType a) (TType b) -> TPi (TType $ tr a) (TType $ tr b)
      TLam b                  -> TLam (tr b)
      TApp a bs               -> TApp (tr a) (map tr bs)
      TLet e b                -> TLet (tr e) (tr b)

      TPlus{} -> __IMPOSSIBLE__

