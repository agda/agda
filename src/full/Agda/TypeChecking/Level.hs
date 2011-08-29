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

data LevelKit = LevelKit
  { lvlType  :: Term
  , lvlSuc   :: Term -> Term
  , lvlMax   :: Term -> Term -> Term
  , lvlZero  :: Term
  , typeName :: QName
  , sucName  :: QName
  , maxName  :: QName
  , zeroName :: QName
  }

levelSucFunction :: MonadTCM tcm => tcm (Term -> Term)
levelSucFunction = do
  suc <- primLevelSuc
  return $ \a -> suc `apply` [defaultArg a]

builtinLevelKit :: MonadTCM tcm => tcm (Maybe LevelKit)
builtinLevelKit = liftTCM $ do
    level@(Def l []) <- primLevel
    zero@(Def z []) <- primLevelZero
    suc@(Def s []) <- primLevelSuc
    max@(Def m []) <- primLevelMax
    let a @@ b = a `apply` [defaultArg b]
    return $ Just $ LevelKit
      { lvlType  = level
      , lvlSuc   = \a -> suc @@ a
      , lvlMax   = \a b -> max @@ a @@ b
      , lvlZero  = zero
      , typeName = l
      , sucName  = s
      , maxName  = m
      , zeroName = z
      }
  `catchError` \_ -> return Nothing

-- | Raises an error if no level kit is available.

requireLevels :: MonadTCM tcm => tcm LevelKit
requireLevels = do
  mKit <- builtinLevelKit
  case mKit of
    Nothing -> sequence_ [primLevel, primLevelZero, primLevelSuc, primLevelMax] >> __IMPOSSIBLE__
    Just k  -> return k

unLevelAtom :: LevelAtom -> Term
unLevelAtom (MetaLevel x as)   = MetaV x as
unLevelAtom (BlockedLevel _ a) = a
unLevelAtom (NeutralLevel a)   = a
unLevelAtom (UnreducedLevel a) = a

reallyUnLevelView :: MonadTCM tcm => Level -> tcm Term
reallyUnLevelView nv =
  case nv of
    Max []              -> primLevelZero
    Max [Plus 0 a]      -> return $ unLevelAtom a
    Max [a]             -> do
      zer <- primLevelZero
      suc <- primLevelSuc
      return $ unPlusV zer (\n -> suc `apply` [defaultArg n]) a
    Max as -> do
      LevelKit{ lvlZero = zer, lvlSuc = suc, lvlMax = max } <- requireLevels
      return $ case map (unPlusV zer suc) as of
        [a] -> a
        []  -> __IMPOSSIBLE__
        as  -> foldr1 max as
  where
    unPlusV zer suc (ClosedLevel n) = foldr (.) id (genericReplicate n suc) zer
    unPlusV _   suc (Plus n a)      = foldr (.) id (genericReplicate n suc) (unLevelAtom a)

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

levelView :: MonadTCM tcm => Term -> tcm Level
levelView a = do
  reportSLn "tc.level.view" 50 $ "{ levelView " ++ show a
  msuc <- maybePrimCon primLevelSuc
  mzer <- maybePrimCon primLevelZero
  mmax <- maybePrimDef primLevelMax
  let view a = do
        a <- reduce a
        case a of
          Level l -> return l
          Con s [arg]
            | Just s == msuc -> inc <$> view (unArg arg)
          Con z []
            | Just z == mzer -> return $ closed 0
          Def m [arg1, arg2]
            | Just m == mmax -> levelLub <$> view (unArg arg1) <*> view (unArg arg2)
          _                  -> mkAtom a
  v <- view a
  reportSLn "tc.level.view" 50 $ "  view: " ++ show v ++ "}"
  return v
  where
    mkAtom a = do
      b <- reduceB a
      return $ case b of
        NotBlocked (MetaV m as) -> atom $ MetaLevel m as
        NotBlocked a            -> atom $ NeutralLevel a
        Blocked m a             -> atom $ BlockedLevel m a

    atom a = Max [Plus 0 a]

    closed n = Max [ClosedLevel n | n > 0]

    inc (Max as) = Max $ map inc' as
      where
        inc' (ClosedLevel n) = ClosedLevel $ n + 1
        inc' (Plus n a)    = Plus (n + 1) a

levelLub :: Level -> Level -> Level
levelLub (Max as) (Max bs) = levelMax $ as ++ bs
