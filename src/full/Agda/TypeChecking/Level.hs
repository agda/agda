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

levelSucFunction :: TCM (Term -> Term)
levelSucFunction = do
  suc <- primLevelSuc
  return $ \a -> suc `apply` [defaultArg a]

builtinLevelKit :: TCM (Maybe LevelKit)
builtinLevelKit = liftTCM $ do
    level@(Def l []) <- ignoreSharing <$> primLevel
    zero@(Def z [])  <- ignoreSharing <$> primLevelZero
    suc@(Def s [])   <- ignoreSharing <$> primLevelSuc
    max@(Def m [])   <- ignoreSharing <$> primLevelMax
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

requireLevels :: TCM LevelKit
requireLevels = do
  mKit <- builtinLevelKit
  case mKit of
    Nothing -> sequence_ [primLevel, primLevelZero, primLevelSuc, primLevelMax] >> __IMPOSSIBLE__
    Just k  -> return k

unLevel :: Term -> TCM Term
unLevel (Level l)  = reallyUnLevelView l
unLevel (Shared p) = unLevel (derefPtr p)
unLevel v = return v

reallyUnLevelView :: Level -> TCM Term
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

maybePrimCon :: TCM Term -> TCM (Maybe QName)
maybePrimCon prim = liftTCM $ do
    Con c [] <- prim
    return (Just c)
  `catchError` \_ -> return Nothing

maybePrimDef :: TCM Term -> TCM (Maybe QName)
maybePrimDef prim = liftTCM $ do
    Def f [] <- prim
    return (Just f)
  `catchError` \_ -> return Nothing

levelView :: Term -> TCM Level
levelView a = do
  reportSLn "tc.level.view" 50 $ "{ levelView " ++ show a
  msuc <- maybePrimCon primLevelSuc
  mzer <- maybePrimCon primLevelZero
  mmax <- maybePrimDef primLevelMax
  let view a = do
        a <- reduce a
        case ignoreSharing a of
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
      return $ case ignoreSharing <$> b of
        NotBlocked (MetaV m as) -> atom $ MetaLevel m as
        NotBlocked _            -> atom $ NeutralLevel (ignoreBlocking b)
        Blocked m _             -> atom $ BlockedLevel m (ignoreBlocking b)

    atom a = Max [Plus 0 a]

    closed n = Max [ClosedLevel n | n > 0]

    inc (Max as) = Max $ map inc' as
      where
        inc' (ClosedLevel n) = ClosedLevel $ n + 1
        inc' (Plus n a)    = Plus (n + 1) a

levelLub :: Level -> Level -> Level
levelLub (Max as) (Max bs) = levelMax $ as ++ bs
