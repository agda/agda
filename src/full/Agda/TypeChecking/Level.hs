{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Level where

import Control.Applicative
import Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad ()
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Except ( MonadError(catchError) )

#include "undefined.h"
import Agda.Utils.Impossible

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

-- | Get the 'primLevel as a 'Term', if present.
mlevel :: TCM (Maybe Term)
mlevel = liftTCM $ (Just <$> primLevel) `catchError` \_ -> return Nothing

-- | Get the 'primLevel' as a 'Type'.
levelType :: TCM Type
levelType = El (mkType 0) <$> primLevel

levelSucFunction :: TCM (Term -> Term)
levelSucFunction = apply1 <$> primLevelSuc

builtinLevelKit :: TCM (Maybe LevelKit)
builtinLevelKit = liftTCM $ do
    level@(Def l []) <- ignoreSharing <$> primLevel
    zero@(Def z [])  <- ignoreSharing <$> primLevelZero
    suc@(Def s [])   <- ignoreSharing <$> primLevelSuc
    max@(Def m [])   <- ignoreSharing <$> primLevelMax
    return $ Just $ LevelKit
      { lvlType  = level
      , lvlSuc   = \ a -> suc `apply1` a
      , lvlMax   = \ a b -> max `applys` [a, b]
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

{-# SPECIALIZE reallyUnLevelView :: Level -> TCM Term #-}
reallyUnLevelView :: MonadTCM tcm => Level -> tcm Term
reallyUnLevelView nv = liftTCM $ do
  case nv of
    Max []              -> primLevelZero
    Max [Plus 0 a]      -> return $ unLevelAtom a
    Max [a]             -> do
      zer <- primLevelZero
      suc <- primLevelSuc
      return $ unPlusV zer (apply1 suc) a
    _ -> (`unlevelWithKit` nv) <$> requireLevels

unlevelWithKit :: LevelKit -> Level -> Term
unlevelWithKit LevelKit{ lvlZero = zer, lvlSuc = suc, lvlMax = max } (Max as) =
  case map (unPlusV zer suc) as of
    [a] -> a
    []  -> zer
    as  -> foldr1 max as

unPlusV :: Term -> (Term -> Term) -> PlusLevel -> Term
unPlusV zer suc (ClosedLevel n) = foldr (.) id (genericReplicate n suc) zer
unPlusV _   suc (Plus n a)      = foldr (.) id (genericReplicate n suc) (unLevelAtom a)

maybePrimCon :: TCM Term -> TCM (Maybe ConHead)
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
  v <- runReduceM $ levelView' a
  reportSLn "tc.level.view" 50 $ "  view: " ++ show v ++ "}"
  return v

levelView' :: Term -> ReduceM Level
levelView' a = do
  msuc <- (getCon =<<) <$> getBuiltin' builtinLevelSuc
  mzer <- (getCon =<<) <$> getBuiltin' builtinLevelZero
  mmax <- (getDef =<<) <$> getBuiltin' builtinLevelMax
  let view a = do
        a <- reduce' a
        case ignoreSharing a of
          Level l -> return l
          Con s [arg]
            | Just s == msuc -> inc <$> view (unArg arg)
          Con z []
            | Just z == mzer -> return $ closed 0
          Def m [Apply arg1, Apply arg2]
            | Just m == mmax -> levelLub <$> view (unArg arg1) <*> view (unArg arg2)
          _                  -> mkAtom a
  v <- view a
  return v
  where
    getCon (Con c []) = Just c
    getCon _          = Nothing

    getDef (Def f []) = Just f
    getDef _          = Nothing

    mkAtom a = do
      b <- reduceB' a
      return $ case ignoreSharing <$> b of
        NotBlocked _ (MetaV m as) -> atom $ MetaLevel m as
        NotBlocked r _            -> atom $ NeutralLevel r $ ignoreBlocking b
        Blocked m _               -> atom $ BlockedLevel m $ ignoreBlocking b

    atom a = Max [Plus 0 a]

    closed n = Max [ClosedLevel n | n > 0]

    inc (Max as) = Max $ map inc' as
      where
        inc' (ClosedLevel n) = ClosedLevel $ n + 1
        inc' (Plus n a)    = Plus (n + 1) a

levelLub :: Level -> Level -> Level
levelLub (Max as) (Max bs) = levelMax $ as ++ bs
