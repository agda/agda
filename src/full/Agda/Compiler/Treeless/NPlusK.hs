-- | Translates the Agda builtin nat datatype to arbitrary-precision integers.
--
-- Philipp, 20150921:
-- At the moment, this optimization is the reason that there is a
-- TAPlus alternative. For Haskell, this can easily be translated to guards. However, in
-- the long term it would be easier for the backends if these things were translated
-- directly to a less-than primitive and if-then-else expressions or similar. This would
-- require us to add some internal Bool-datatype as compiler-internal type and
-- a primitive less-than function, which will be much easier once Treeless
-- is used for whole modules.
--
-- Ulf, 2015-09-21: No, actually we need the n+k patterns, or at least guards.
-- Representing them with if-then-else would make it a lot harder to do
-- optimisations that analyse case tree, like impossible case elimination.
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module Agda.Compiler.Treeless.NPlusK (introduceNPlusK) where

import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position
import Agda.Syntax.Treeless
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.Compiler.Treeless.Subst

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

      TCon c | isZero c -> tInt 0
             | isSuc c  -> TLam (tPlusK 1 (TVar 0))
      TApp (TCon s) [e] | isSuc s ->
        case tr e of
          TLit (LitNat r n) -> tInt (n + 1)
          e | Just (i, e) <- plusKView e -> tPlusK (i + 1) e
          e                 -> tPlusK 1 e

      TCase e t d bs -> TCase e t (tr d) $ concatMap trAlt bs
        where
          trAlt b = case b of
            TACon c 0 b | isZero c -> [TALit (LitNat noRange 0) (tr b)]
            TACon c 1 b | isSuc c  ->
              case tr b of
                -- Collapse nested n+k patterns
                TCase 0 _ d bs' -> map sucBranch bs' ++ [nPlusKAlt 1 d]
                b -> [nPlusKAlt 1 b]
              where
                sucBranch (TALit (LitNat r i) b) = TALit (LitNat r (i + 1)) $ applySubst (str __IMPOSSIBLE__) b
                sucBranch alt | Just (k, b) <- nPlusKView alt = nPlusKAlt (k + 1) $ applySubst (liftS 1 $ str __IMPOSSIBLE__) b
                sucBranch _ = __IMPOSSIBLE__

                nPlusKAlt k b = TAGuard (tOp PGeq (TVar e) (tInt k)) $
                                TLet (tOp PSub (TVar e) (tInt k)) b

                nPlusKView (TAGuard (TApp (TPrim PGeq) [TVar 0, (TLit (LitNat _ k))])
                                    (TLet (TApp (TPrim PSub) [TVar 0, (TLit (LitNat _ j))]) b))
                  | k == j = Just (k, b)
                nPlusKView _ = Nothing

                str err = compactS err [Nothing]

            TACon c a b -> [TACon c a (tr b)]
            TALit{}     -> [b]
            TAGuard{}   -> __IMPOSSIBLE__

      TVar{}    -> t
      TDef{}    -> t
      TCon{}    -> t
      TPrim{}   -> t
      TLit{}    -> t
      TUnit{}   -> t
      TSort{}   -> t
      TErased{} -> t
      TError{}  -> t

      TLam b                  -> TLam (tr b)
      TApp a bs               -> TApp (tr a) (map tr bs)
      TLet e b                -> TLet (tr e) (tr b)

