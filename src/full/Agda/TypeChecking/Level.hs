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
  deriving (Show, Eq)

data LevelAtom = MetaLevel MetaId Args
             | BlockedLevel Term
             | NeutralLevel Term
  deriving (Show, Eq, Ord)

instance Ord PlusView where
  compare ClosedLevel{} Plus{}            = LT
  compare Plus{} ClosedLevel{}            = GT
  compare (ClosedLevel n) (ClosedLevel m) = compare n m
  compare (Plus n a) (Plus m b)           = compare (a,n) (b,m)


data LevelKit = LevelKit
  { levelType  :: Term
  , levelSuc   :: Term -> Term
  , levelMax   :: Term -> Term -> Term
  , levelZero  :: Term
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
    zero@(Con z []) <- primLevelZero
    suc@(Con s []) <- primLevelSuc
    max@(Def m []) <- primLevelMax
    let a @@ b = a `apply` [defaultArg b]
    return $ Just $ LevelKit
      { levelType = level
      , levelSuc = \a -> suc @@ a
      , levelMax = \a b -> max @@ a @@ b
      , levelZero = zero
      , typeName = l
      , sucName = s
      , maxName = m
      , zeroName = z
      }
  `catchError` \_ -> return Nothing

-- | Raises an error if no level kit is available.

requireLevels :: TCM LevelKit
requireLevels = do
  mKit <- builtinLevelKit
  case mKit of
    Nothing -> typeError $ GenericError $
      "Some or all of the LEVEL builtins have not been defined."
    Just k  -> return k

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
      return $ unPlusV (\n -> suc `apply` [defaultArg n]) a
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
          Con s [arg]
            | Just s == msuc -> inc <$> view (unArg arg)
          Con z []
            | Just z == mzer -> return $ closed 0
          Lit (LitLevel _ n)   -> return $ closed n
          Def m [arg1, arg2]
            | Just m == mmax -> lub <$> view (unArg arg1) <*> view (unArg arg2)
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

    maxim as = Max $ ns ++ List.sort bs
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

