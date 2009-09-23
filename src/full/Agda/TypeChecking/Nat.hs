{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Nat where

import Control.Monad.Error
import Control.Applicative
import Data.List as List

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Impossible
#include "../undefined.h"

newtype NatView = Max [PlusView]
  deriving (Show)

data PlusView = ClosedNat Integer
              | Plus Integer NatAtom
  deriving (Show, Eq, Ord)

data NatAtom = MetaNat MetaId Args
             | BlockedNat Term
             | NeutralNat Term
  deriving (Show, Eq, Ord)

data NatKit = NatKit
  { natSuc   :: Term -> Term
  , natMax   :: Term -> Term -> Term
  , sucName  :: QName
  , maxName  :: QName
  , zeroName :: QName
  }

builtinNatKit :: MonadTCM tcm => tcm (Maybe NatKit)
builtinNatKit = liftTCM $ do
    Con z [] <- primZero
    suc@(Con s []) <- primSuc
    max@(Def m []) <- primNatMax
    let a @@ b = a `apply` [Arg NotHidden b]
    return $ Just $ NatKit
      { natSuc = \a -> suc @@ a
      , natMax = \a b -> max @@ a @@ b
      , sucName = s
      , maxName = m
      , zeroName = z
      }
  `catchError` \_ -> return Nothing

unNatAtom :: NatAtom -> Term
unNatAtom (MetaNat x as) = MetaV x as
unNatAtom (BlockedNat a) = a
unNatAtom (NeutralNat a) = a

unNatView :: MonadTCM tcm => NatView -> tcm Term
unNatView nv = case nv of
    Max []            -> return $ Lit $ LitInt noRange 0
    Max [ClosedNat n] -> return $ Lit $ LitInt noRange n
    Max [Plus 0 a]    -> return $ unNatAtom a
    Max [a]           -> do
      suc <- primSuc
      return $ unPlusV (\n -> suc `apply` [Arg NotHidden n]) a
    Max as -> do
      Just NatKit{ natSuc = suc, natMax = max } <- builtinNatKit
      return $ case map (unPlusV suc) as of
        [a] -> a
        []  -> __IMPOSSIBLE__
        as  -> foldr1 max as
  where
    unPlusV suc (ClosedNat n) = Lit (LitInt noRange n)
    unPlusV suc (Plus n a)    = foldr (.) id (genericReplicate n suc) (unNatAtom a)

maybePrimCon :: MonadTCM tcm => TCM Term -> tcm (Maybe QName)
maybePrimCon prim = liftTCM $ do
    Con c [] <- prim
    return (Just c)
  `catchError` \_ -> return Nothing

maybePrimDef :: MonadTCM tcm => TCM Term -> tcm (Maybe QName)
maybePrimDef prim = liftTCM $ do
    Def f [] <- prim
    return (Just f)
  `catchError` \_ -> return Nothing

natView :: MonadTCM tcm => Term -> tcm NatView
natView a = do
  msuc <- maybePrimCon primSuc
  mzer <- maybePrimCon primZero
  mmax <- maybePrimDef primNatMax
  let view a =
        case a of
          Con s [Arg NotHidden a]
            | Just s == msuc -> inc <$> view a
          Con z []
            | Just z == mzer -> return $ closed 0
          Lit (LitInt _ n)   -> return $ closed n
          Def m [Arg NotHidden a, Arg NotHidden b]
            | Just m == mmax -> lub <$> view a <*> view b
          _                  -> mkAtom a
  view =<< normalise a
  where
    mkAtom a = do
      b <- reduceB a
      return $ case b of
        NotBlocked (MetaV m as) -> atom $ MetaNat m as
        NotBlocked a            -> atom $ NeutralNat a
        Blocked _ a             -> atom $ BlockedNat a

    atom a = Max [Plus 0 a]

    closed n = maxim [ClosedNat n]

    inc (Max as) = Max $ map inc' as
      where
        inc' (ClosedNat n) = ClosedNat $ n + 1
        inc' (Plus n a)    = Plus (n + 1) a

    maxim as = Max $ ns ++ bs
      where
        ns = case [ n | ClosedNat n <- as, n > 0 ] of
          []  -> []
          ns  -> [ClosedNat $ maximum ns]
        bs = subsume [ b | b@Plus{} <- as ]
        
        subsume (ClosedNat{} : _) = __IMPOSSIBLE__
        subsume [] = []
        subsume (Plus n a : bs)
          | not $ null ns = subsume bs
          | otherwise     = Plus n a : subsume [ b | b@(Plus _ a') <- bs, a /= a' ]
          where
            ns = [ m | Plus m a'  <- bs, a == a', m > n ]

    lub (Max as) (Max bs) = maxim $ as ++ bs

