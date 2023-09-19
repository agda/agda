
module Agda.TypeChecking.Level where

import Data.Maybe
import qualified Data.List as List
import Data.Traversable (Traversable)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce

import Agda.Utils.List1 ( List1, pattern (:|) )
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

{-# SPECIALIZE levelType :: TCM Type #-}
-- | Get the 'primLevel' as a 'Type'.  Aborts if any of the level BUILTINs is undefined.
levelType :: (HasBuiltins m, MonadTCError m) => m Type
levelType =
  El LevelUniv . lvlType <$> requireLevels
  -- Andreas, 2022-10-11, issue #6168
  -- It seems superfluous to require all level builtins here,
  -- but since we are in MonadTCError here, this is our chance to make sure
  -- that all level builtins are defined.
  -- Otherwise, we might run into an __IMPOSSIBLE__ later,
  -- e.g. if only BUILTIN LEVEL was defined by reallyUnLevelView requires all builtins.

{-# SPECIALIZE levelType' :: TCM Type #-}
-- | Get the 'primLevel' as a 'Type'.  Unsafe, crashes if the BUILTIN LEVEL is undefined.
levelType' :: (HasBuiltins m) => m Type
levelType' =
  El LevelUniv . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel

{-# SPECIALIZE isLevelType :: Type -> TCM Bool #-}
isLevelType :: PureTCM m => Type -> m Bool
isLevelType a = reduce (unEl a) >>= \case
  Def f [] -> do
    Def lvl [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    return $ f == lvl
  _ -> return False

{-# SPECIALIZE builtinLevelKit :: TCM LevelKit #-}
{-# SPECIALIZE builtinLevelKit :: ReduceM LevelKit #-}
builtinLevelKit :: (HasBuiltins m) => m LevelKit
builtinLevelKit = do
    level@(Def l [])     <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevel
    zero@(Def z [])      <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelZero
    suc@(Def s [])       <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelSuc
    max@(Def m [])       <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinLevelMax
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

{-# SPECIALIZE requireLevels :: TCM LevelKit #-}
-- | Raises an error if no level kit is available.
requireLevels :: (HasBuiltins m, MonadTCError m) => m LevelKit
requireLevels = do
    level@(Def l [])     <- getBuiltin builtinLevel
    zero@(Def z [])      <- getBuiltin builtinLevelZero
    suc@(Def s [])       <- getBuiltin builtinLevelSuc
    max@(Def m [])       <- getBuiltin builtinLevelMax
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

-- | Checks whether level kit is fully available.
haveLevels :: HasBuiltins m => m Bool
haveLevels = caseMaybeM (allJustM $ map getBuiltin' levelBuiltins)
    (return False)
    (\ _bs -> return True)
  where
  levelBuiltins =
    [ builtinLevelUniv
    , builtinLevel
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
reallyUnLevelView nv = (`unlevelWithKit` nv) <$> builtinLevelKit

unlevelWithKit :: LevelKit -> Level -> Term
unlevelWithKit LevelKit{ lvlZero = zer, lvlSuc = suc, lvlMax = max } = \case
  Max m []  -> unConstV zer suc m
  Max 0 [a] -> unPlusV suc a
  Max m as  -> foldl1 max $ [ unConstV zer suc m | m > 0 ] ++ map (unPlusV suc) as

unConstV :: Term -> (Term -> Term) -> Integer -> Term
unConstV zer suc n = foldr ($) zer (List.genericReplicate n suc)

unPlusV :: (Term -> Term) -> PlusLevel -> Term
unPlusV suc (Plus n a) = foldr ($) a (List.genericReplicate n suc)

maybePrimCon :: TCM Term -> TCM (Maybe ConHead)
maybePrimCon prim = tryMaybe $ do
    Con c ci [] <- prim
    return c

maybePrimDef :: TCM Term -> TCM (Maybe QName)
maybePrimDef prim = tryMaybe $ do
    Def f [] <- prim
    return f

{-# SPECIALIZE levelView :: Term -> TCM Level #-}
levelView :: PureTCM m => Term -> m Level
levelView a = do
  reportSLn "tc.level.view" 50 $ "{ levelView " ++ show a
  v <- levelView' a
  reportSLn "tc.level.view" 50 $ "  view: " ++ show v ++ "}"
  return v

{-# SPECIALIZE levelView' :: Term -> TCM Level #-}
levelView' :: PureTCM m => Term -> m Level
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
          l              -> return $ atomicLevel l
  view a

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
--   Operates on levels in canonical form.
subLevel :: Integer -> Level -> Maybe Level
subLevel n (Max m ls) = Max <$> m' <*> traverse subPlus ls
  where
    m' :: Maybe Integer
    m' | m == 0, not (null ls) = Just 0
       | otherwise             = sub m

    -- General purpose function.
    nonNeg :: Integer -> Maybe Integer
    nonNeg j | j >= 0 = Just j
             | otherwise = Nothing

    sub :: Integer -> Maybe Integer
    sub = nonNeg . subtract n

    subPlus :: PlusLevel -> Maybe PlusLevel
    subPlus (Plus j l) = Plus <$> sub j <*> Just l

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
data SingleLevel' t = SingleClosed Integer | SinglePlus (PlusLevel' t)
  deriving (Show, Functor, Foldable, Traversable)

type SingleLevel = SingleLevel' Term

deriving instance Eq SingleLevel

unSingleLevel :: SingleLevel' t -> Level' t
unSingleLevel (SingleClosed m) = Max m []
unSingleLevel (SinglePlus a)   = Max 0 [a]

-- | Return the maximum of the given @SingleLevel@s
unSingleLevels :: [SingleLevel] -> Level
unSingleLevels ls = levelMax n as
  where
    n = maximum $ 0 : [m | SingleClosed m <- ls]
    as = [a | SinglePlus a <- ls]

levelMaxView :: Level' t -> List1 (SingleLevel' t)
levelMaxView (Max n [])     = singleton $ SingleClosed n
levelMaxView (Max 0 (a:as)) = SinglePlus a :| map SinglePlus as
levelMaxView (Max n as)     = SingleClosed n :| map SinglePlus as

singleLevelView :: Level' t -> Maybe (SingleLevel' t)
singleLevelView l = case levelMaxView l of
  s :| [] -> Just s
  _       -> Nothing

instance Subst t => Subst (SingleLevel' t) where
  type SubstArg (SingleLevel' t) = SubstArg t

  applySubst sub (SingleClosed m) = SingleClosed m
  applySubst sub (SinglePlus a)   = SinglePlus $ applySubst sub a

instance Free t => Free (SingleLevel' t) where
  freeVars' (SingleClosed m) = mempty
  freeVars' (SinglePlus a)   = freeVars' a
