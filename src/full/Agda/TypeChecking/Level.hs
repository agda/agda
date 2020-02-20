
module Agda.TypeChecking.Level where

import Data.Maybe
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Maybe ( caseMaybeM, allJustM )
import Agda.Utils.Monad ( tryMaybe )
import Agda.Utils.Singleton

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
    Max n []       -> return $ unConstV zer (apply1 suc) n
    Max 0 [a]      -> return $ unPlusV (apply1 suc) a
    _              -> (`unlevelWithKit` nv) <$> builtinLevelKit

unlevelWithKit :: LevelKit -> Level -> Term
unlevelWithKit LevelKit{ lvlZero = zer, lvlSuc = suc, lvlMax = max } = \case
  Max m []  -> unConstV zer suc m
  Max 0 [a] -> unPlusV suc a
  Max m as  -> foldl1 max $ [ unConstV zer suc m | m > 0 ] ++ map (unPlusV suc) as

unConstV :: Term -> (Term -> Term) -> Integer -> Term
unConstV zer suc n = foldr (.) id (List.genericReplicate n suc) zer

unPlusV :: (Term -> Term) -> PlusLevel -> Term
unPlusV suc (Plus n a) = foldr (.) id (List.genericReplicate n suc) (unLevelAtom a)

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
        ba <- reduceB a
        case ignoreBlocking ba of
          Level l -> return l
          Def s [Apply arg]
            | s == lsuc  -> levelSuc <$> view (unArg arg)
          Def z []
            | z == lzero -> return $ ClosedLevel 0
          Def m [Apply arg1, Apply arg2]
            | m == lmax  -> levelLub <$> view (unArg arg1) <*> view (unArg arg2)
          _              -> return $ mkAtom ba
  view a
  where
    mkAtom ba = atomicLevel $ case ba of
        NotBlocked _ (MetaV m as) -> MetaLevel m as
        NotBlocked r _            -> case r of
          StuckOn{}               -> NeutralLevel r $ ignoreBlocking ba
          Underapplied{}          -> NeutralLevel r $ ignoreBlocking ba
          AbsurdMatch{}           -> NeutralLevel r $ ignoreBlocking ba
          MissingClauses{}        -> UnreducedLevel $ ignoreBlocking ba
          ReallyNotBlocked{}      -> NeutralLevel r $ ignoreBlocking ba
        Blocked m _               -> BlockedLevel m $ ignoreBlocking ba

-- | Given a level @l@, find the maximum constant @n@ such that @l = n + l'@
levelPlusView :: Level -> (Integer, Level)
levelPlusView (Max 0 []) = (0 , Max 0 [])
levelPlusView (Max 0 as@(_:_)) = (minN , Max 0 (map sub as))
  where
    minN = minimum [ n | Plus n _ <- as ]
    sub (Plus n a) = Plus (n - minN) a
levelPlusView (Max n as) = (minN , Max (n - minN) (map sub as))
  where
    minN = minimum $ n : [ n' | Plus n' _ <- as ]
    sub (Plus n' a) = Plus (n' - minN) a

-- | Given a level @l@, find the biggest constant @n@ such that @n <= l@
levelLowerBound :: Level -> Integer
levelLowerBound (Max m as) = maximum $ m : [n | Plus n _ <- as]

-- | Given a constant @n@ and a level @l@, find the level @l'@ such
--   that @l = n + l'@ (or Nothing if there is no such level).
subLevel :: Integer -> Level -> Maybe Level
subLevel n (Max m ls)
  | m == 0    = Max 0 <$> traverse sub ls
  | m >= n    = Max (m - n) <$> traverse sub ls
  | otherwise = Nothing
  where
    sub :: PlusLevel -> Maybe PlusLevel
    sub (Plus j l) | j >= n    = Just $ Plus (j - n) l
                   | otherwise = Nothing


-- | Given two levels @a@ and @b@, try to decompose the first one as
-- @a = a' ⊔ b@ (for the minimal value of @a'@).
levelMaxDiff :: Level -> Level -> Maybe Level
levelMaxDiff (Max m as) (Max n bs) = Max <$> diffC m n <*> diffP as bs
  where
    diffC :: Integer -> Integer -> Maybe Integer
    diffC m n
      | m == n    = Just 0
      | m > n     = Just m
      | otherwise = Nothing

    diffP :: [PlusLevel] -> [PlusLevel] -> Maybe [PlusLevel]
    diffP as     []     = Just as
    diffP []     bs     = Nothing
    diffP (a@(Plus m x) : as) (b@(Plus n y) : bs)
      | x == y = if
        | m == n    -> diffP as bs
        | m > n     -> (Plus m x:) <$> diffP as bs
        | otherwise -> Nothing
      | otherwise = (a:) <$> diffP as (b:bs)

-- | A @SingleLevel@ is a @Level@ that cannot be further decomposed as
--   a maximum @a ⊔ b@.
data SingleLevel = SingleClosed Integer | SinglePlus PlusLevel
  deriving (Eq, Show)

unSingleLevel :: SingleLevel -> Level
unSingleLevel (SingleClosed m) = Max m []
unSingleLevel (SinglePlus a)   = Max 0 [a]

-- | Return the maximum of the given @SingleLevel@s
unSingleLevels :: [SingleLevel] -> Level
unSingleLevels ls = levelMax n as
  where
    n = maximum $ 0 : [m | SingleClosed m <- ls]
    as = [a | SinglePlus a <- ls]

levelMaxView :: Level -> NonEmpty SingleLevel
levelMaxView (Max n [])     = singleton $ SingleClosed n
levelMaxView (Max 0 (a:as)) = SinglePlus a :| map SinglePlus as
levelMaxView (Max n as)     = SingleClosed n :| map SinglePlus as

singleLevelView :: Level -> Maybe SingleLevel
singleLevelView l = case levelMaxView l of
  s :| [] -> Just s
  _       -> Nothing

instance Subst Term SingleLevel where
  applySubst sub (SingleClosed m) = SingleClosed m
  applySubst sub (SinglePlus a)   = SinglePlus $ applySubst sub a

instance Free SingleLevel where
  freeVars' (SingleClosed m) = mempty
  freeVars' (SinglePlus a)   = freeVars' a
