
module Agda.TypeChecking.Level where

import Data.Maybe
import qualified Data.List as List
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Maybe ( caseMaybeM, allJustM )
import Agda.Utils.Monad ( tryMaybe )

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

-- | Get the 'primLevel' as a 'Type'.
levelType :: (HasBuiltins m) => m Type
levelType = El (mkType 0) . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel

isLevelType :: (HasBuiltins m, MonadReduce m) => Type -> m Bool
isLevelType a = reduce (unEl a) >>= \case
  Def f [] -> do
    Def lvl [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    return $ f == lvl
  _ -> return False

levelSucFunction :: TCM (Term -> Term)
levelSucFunction = apply1 <$> primLevelSuc

{-# SPECIALIZE builtinLevelKit :: TCM LevelKit #-}
{-# SPECIALIZE builtinLevelKit :: ReduceM LevelKit #-}
builtinLevelKit :: (HasBuiltins m) => m LevelKit
builtinLevelKit = do
    level@(Def l []) <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    zero@(Def z [])  <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelZero
    suc@(Def s [])   <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelSuc
    max@(Def m [])   <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelMax
    return $ LevelKit
      { lvlType  = level
      , lvlSuc   = \ a -> suc `apply1` a
      , lvlMax   = \ a b -> max `applys` [a, b]
      , lvlZero  = zero
      , typeName = l
      , sucName  = s
      , maxName  = m
      , zeroName = z
      }

-- | Raises an error if no level kit is available.
requireLevels :: HasBuiltins m => m LevelKit
requireLevels = builtinLevelKit

-- | Checks whether level kit is fully available.
haveLevels :: HasBuiltins m => m Bool
haveLevels = caseMaybeM (allJustM $ map getBuiltin' levelBuiltins)
    (return False)
    (\ _bs -> return True)
  where
  levelBuiltins =
    [ builtinLevel
    , builtinLevelZero
    , builtinLevelSuc
    , builtinLevelMax
    ]

{-# SPECIALIZE unLevel :: Term -> TCM Term #-}
{-# SPECIALIZE unLevel :: Term -> ReduceM Term #-}
unLevel :: (HasBuiltins m) => Term -> m Term
unLevel (Level l)  = reallyUnLevelView l
unLevel v = return v

{-# SPECIALIZE reallyUnLevelView :: Level -> TCM Term #-}
{-# SPECIALIZE reallyUnLevelView :: Level -> ReduceM Term #-}
reallyUnLevelView :: (HasBuiltins m) => Level -> m Term
reallyUnLevelView nv = do
  suc <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelSuc
  zer <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelZero
  case nv of
    Max []              -> return zer
    Max [Plus 0 a]      -> return $ unLevelAtom a
    Max [a]             -> do
      return $ unPlusV zer (apply1 suc) a
    _ -> (`unlevelWithKit` nv) <$> builtinLevelKit

unlevelWithKit :: LevelKit -> Level -> Term
unlevelWithKit LevelKit{ lvlZero = zer, lvlSuc = suc, lvlMax = max } (Max as) =
  case map (unPlusV zer suc) as of
    [a] -> a
    []  -> zer
    as  -> foldl1 max as

unPlusV :: Term -> (Term -> Term) -> PlusLevel -> Term
unPlusV zer suc (ClosedLevel n) = foldr (.) id (List.genericReplicate n suc) zer
unPlusV _   suc (Plus n a)      = foldr (.) id (List.genericReplicate n suc) (unLevelAtom a)

maybePrimCon :: TCM Term -> TCM (Maybe ConHead)
maybePrimCon prim = tryMaybe $ do
    Con c ci [] <- prim
    return c

maybePrimDef :: TCM Term -> TCM (Maybe QName)
maybePrimDef prim = tryMaybe $ do
    Def f [] <- prim
    return f

levelView :: (HasBuiltins m, MonadReduce m, MonadDebug m)
          => Term -> m Level
levelView a = do
  reportSLn "tc.level.view" 50 $ "{ levelView " ++ show a
  v <- levelView' a
  reportSLn "tc.level.view" 50 $ "  view: " ++ show v ++ "}"
  return v

levelView' :: (HasBuiltins m, MonadReduce m, MonadDebug m)
           => Term -> m Level
levelView' a = do
  Def lzero [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelZero
  Def lsuc  [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelSuc
  Def lmax  [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelMax
  let view a = do
        a <- reduce a
        case a of
          Level l -> return l
          Def s [Apply arg]
            | s == lsuc  -> inc <$> view (unArg arg)
          Def z []
            | z == lzero -> return $ closed 0
          Def m [Apply arg1, Apply arg2]
            | m == lmax  -> levelLub <$> view (unArg arg1) <*> view (unArg arg2)
          _              -> mkAtom a
  v <- view a
  return v
  where
    mkAtom a = do
      b <- reduceB a
      return $ case b of
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

subLevel :: Integer -> Level -> Maybe Level
subLevel n (Max ls) = Max <$> traverse sub ls
  where
    sub :: PlusLevel -> Maybe PlusLevel
    sub (ClosedLevel j) | j >= n    = Just $ ClosedLevel $ j - n
                        | otherwise = Nothing
    sub (Plus j l)      | j >= n    = Just $ Plus (j - n) l
                        | otherwise = Nothing
