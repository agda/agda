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
--
-- Ulf, 2015-10-30: Guards are actually a better primitive. Fixed that.
{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.Builtin (translateBuiltins) where

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

data BuiltinKit = BuiltinKit
  { isZero   :: QName -> Bool
  , isSuc    :: QName -> Bool
  , isPos    :: QName -> Bool
  , isNegSuc :: QName -> Bool
  , isPlus   :: QName -> Bool
  , isTimes  :: QName -> Bool
  , isLess   :: QName -> Bool
  , isEqual  :: QName -> Bool
  , isForce  :: QName -> Bool
  }

builtinKit :: TCM BuiltinKit
builtinKit =
  BuiltinKit <$> isB con builtinZero
             <*> isB con builtinSuc
             <*> isB con builtinIntegerPos
             <*> isB con builtinIntegerNegSuc
             <*> isB def builtinNatPlus
             <*> isB def builtinNatTimes
             <*> isB def builtinNatLess
             <*> isB def builtinNatEquals
             <*> isP pf  "primForce"
  where
    con (I.Con c _ _) = pure $ I.conName c
    con _           = Nothing
    def (I.Def d _) = pure d
    def _           = Nothing

    pf = Just . primFunName

    is  a b = maybe (const False) (==) . (a =<<) <$> b
    isB a b = is a (getBuiltin' b)
    isP a p = is a (getPrimitive' p)

translateBuiltins :: TTerm -> TCM TTerm
translateBuiltins t = do
  kit <- builtinKit
  return $ transform kit t

transform :: BuiltinKit -> TTerm -> TTerm
transform BuiltinKit{..} = tr
  where
    tr t = case t of

      TCon c | isZero c   -> tInt 0
             | isSuc c    -> TLam (tPlusK 1 (TVar 0))
             | isPos c    -> TLam (TVar 0)
             | isNegSuc c -> TLam $ tNegPlusK 1 (TVar 0)

      TDef f | isPlus f   -> TPrim PAdd
             | isTimes f  -> TPrim PMul
             | isLess f   -> TPrim PLt
             | isEqual f  -> TPrim PEqI
        -- Note: Don't do this for builtinNatMinus! PSub is integer minus and
        --       builtin minus is monus. The simplifier will do it if it can see
        --       that it won't underflow.

      TApp (TDef q) [_, _, _, _, e, f]
        | isForce q -> tr $ TLet e $ tOp PSeq (TVar 0) $ mkTApp (raise 1 f) [TVar 0]

      TApp (TCon s) [e] | isSuc s ->
        case tr e of
          TLit (LitNat r n) -> tInt (n + 1)
          e | Just (i, e) <- plusKView e -> tPlusK (i + 1) e
          e                 -> tPlusK 1 e

      TApp (TCon c) [e]
        | isPos c    -> tr e
        | isNegSuc c ->
        case tr e of
          TLit (LitNat _ n) -> tInt (-n - 1)
          e | Just (i, e) <- plusKView e -> tNegPlusK (i + 1) e
          e -> tNegPlusK 1 e

      TCase e t d bs -> TCase e (caseType t bs) (tr d) $ concatMap trAlt bs
        where
          trAlt b = case b of
            TACon c 0 b | isZero c -> [TALit (LitNat noRange 0) (tr b)]
            TACon c 1 b | isSuc c  ->
              case tr b of
                -- Collapse nested n+k patterns
                TCase 0 _ d bs' -> map sucBranch bs' ++ [nPlusKAlt 1 d]
                b -> [nPlusKAlt 1 b]
              where
                sucBranch (TALit (LitNat r i) b) = TALit (LitNat r (i + 1)) $ TLet (tInt i) b
                sucBranch alt | Just (k, b) <- nPlusKView alt =
                  nPlusKAlt (k + 1) $ TLet (tOp PAdd (TVar 0) (tInt 1)) $
                    applySubst ([TVar 1, TVar 0] ++# wkS 2 idS) b
                sucBranch _ = __IMPOSSIBLE__

                nPlusKAlt k b = TAGuard (tOp PGeq (TVar e) (tInt k)) $
                                TLet (tOp PSub (TVar e) (tInt k)) b

                str err = compactS err [Nothing]

            TACon c 1 b | isPos c ->
              case tr b of
                -- collapse nested nat patterns
                TCase 0 _ d bs -> map sub bs ++ [posAlt d]
                b -> [posAlt  b]
              where
                -- subst scrutinee for the pos argument
                sub :: Subst TTerm a => a -> a
                sub = applySubst (TVar e :# IdS)

                posAlt b = TAGuard (tOp PGeq (TVar e) (tInt 0)) $ sub b

            TACon c 1 b | isNegSuc c ->
              case tr b of
                -- collapse nested nat patterns
                TCase 0 _ d bs -> map negsucBranch bs ++ [negAlt d]
                b -> [negAlt b]
              where
                body b   = TLet (tNegPlusK 1 (TVar e)) b
                negAlt b = TAGuard (tOp PLt (TVar e) (tInt 0)) $ body b

                negsucBranch (TALit (LitNat r i) b) = TALit (LitNat r (-i - 1)) $ body b
                negsucBranch alt | Just (k, b) <- nPlusKView alt =
                  TAGuard (tOp PLt (TVar e) (tInt (-k))) $
                  body $ TLet (tNegPlusK (k + 1) (TVar $ e + 1)) b
                negsucBranch _ = __IMPOSSIBLE__


            TACon c a b -> [TACon c a (tr b)]
            TALit l b   -> [TALit l (tr b)]
            TAGuard g b -> [TAGuard (tr g) (tr b)]

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

    caseType t (TACon c _ _ : _)
      | isZero c   = CTNat
      | isSuc c    = CTNat
      | isPos c    = CTInt
      | isNegSuc c = CTInt
    caseType t _ = t

    nPlusKView (TAGuard (TApp (TPrim PGeq) [TVar 0, (TLit (LitNat _ k))])
                        (TLet (TApp (TPrim PSub) [TVar 0, (TLit (LitNat _ j))]) b))
      | k == j = Just (k, b)
    nPlusKView _ = Nothing
