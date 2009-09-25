{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Level where

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

newtype LevelView = Max [PlusView]
  deriving (Show)

data PlusView = ClosedLevel Integer
              | Plus Integer LevelAtom
  deriving (Show, Eq, Ord)

data LevelAtom = MetaLevel MetaId Args
             | BlockedLevel Term
             | NeutralLevel Term
  deriving (Show, Eq, Ord)

data LevelKit = LevelKit
  { levelSuc   :: Term -> Term
  , levelMax   :: Term -> Term -> Term
  , sucName  :: QName
  , maxName  :: QName
  , zeroName :: QName
  }

builtinLevelKit :: MonadTCM tcm => tcm (Maybe LevelKit)
builtinLevelKit = liftTCM $ do
    Con z [] <- primLevelZero
    suc@(Con s []) <- primLevelSuc
    max@(Def m []) <- primLevelMax
    let a @@ b = a `apply` [Arg NotHidden b]
    return $ Just $ LevelKit
      { levelSuc = \a -> suc @@ a
      , levelMax = \a b -> max @@ a @@ b
      , sucName = s
      , maxName = m
      , zeroName = z
      }
  `catchError` \_ -> return Nothing

unLevelAtom :: LevelAtom -> Term
unLevelAtom (MetaLevel x as) = MetaV x as
unLevelAtom (BlockedLevel a) = a
unLevelAtom (NeutralLevel a) = a

unLevelView :: MonadTCM tcm => LevelView -> tcm Term
unLevelView nv = case nv of
    Max []            -> return $ Lit $ LitLevel noRange 0
    Max [ClosedLevel n] -> return $ Lit $ LitLevel noRange n
    Max [Plus 0 a]    -> return $ unLevelAtom a
    Max [a]           -> do
      suc <- primLevelSuc
      return $ unPlusV (\n -> suc `apply` [Arg NotHidden n]) a
    Max as -> do
      Just LevelKit{ levelSuc = suc, levelMax = max } <- builtinLevelKit
      return $ case map (unPlusV suc) as of
        [a] -> a
        []  -> __IMPOSSIBLE__
        as  -> foldr1 max as
  where
    unPlusV suc (ClosedLevel n) = Lit (LitLevel noRange n)
    unPlusV suc (Plus n a)    = foldr (.) id (genericReplicate n suc) (unLevelAtom a)

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

levelView :: MonadTCM tcm => Term -> tcm LevelView
levelView a = do
  msuc <- maybePrimCon primLevelSuc
  mzer <- maybePrimCon primLevelZero
  mmax <- maybePrimDef primLevelMax
  let view a =
        case a of
          Con s [Arg NotHidden a]
            | Just s == msuc -> inc <$> view a
          Con z []
            | Just z == mzer -> return $ closed 0
          Lit (LitLevel _ n)   -> return $ closed n
          Def m [Arg NotHidden a, Arg NotHidden b]
            | Just m == mmax -> lub <$> view a <*> view b
          _                  -> mkAtom a
  view =<< normalise a
  where
    mkAtom a = do
      b <- reduceB a
      return $ case b of
        NotBlocked (MetaV m as) -> atom $ MetaLevel m as
        NotBlocked a            -> atom $ NeutralLevel a
        Blocked _ a             -> atom $ BlockedLevel a

    atom a = Max [Plus 0 a]

    closed n = maxim [ClosedLevel n]

    inc (Max as) = Max $ map inc' as
      where
        inc' (ClosedLevel n) = ClosedLevel $ n + 1
        inc' (Plus n a)    = Plus (n + 1) a

    maxim as = Max $ ns ++ bs
      where
        ns = case [ n | ClosedLevel n <- as, n > 0 ] of
          []  -> []
          ns  -> [ClosedLevel $ maximum ns]
        bs = subsume [ b | b@Plus{} <- as ]
        
        subsume (ClosedLevel{} : _) = __IMPOSSIBLE__
        subsume [] = []
        subsume (Plus n a : bs)
          | not $ null ns = subsume bs
          | otherwise     = Plus n a : subsume [ b | b@(Plus _ a') <- bs, a /= a' ]
          where
            ns = [ m | Plus m a'  <- bs, a == a', m > n ]

    lub (Max as) (Max bs) = maxim $ as ++ bs

