{-# LANGUAGE CPP, TupleSections #-}
module Agda.TypeChecking.Monad.SizedTypes where

import Control.Applicative
import Control.Monad.Error

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Builtin
-- import Agda.TypeChecking.Reduce -- cyclic
import Agda.TypeChecking.Substitute

import Agda.Utils.Monad
import Agda.Utils.Impossible
#include "../../undefined.h"

------------------------------------------------------------------------
-- * Testing for type 'Size'
------------------------------------------------------------------------

-- | Result of querying whether size variable @i@ is bounded by another
--   size.
data BoundedSize
  =  BoundedLt Term -- ^ yes @i : Size< t@
  |  BoundedNo
     deriving (Eq, Show)

-- | Check if a type is the 'primSize' type. The argument should be 'reduce'd.
isSizeType :: Type -> TCM (Maybe BoundedSize)
isSizeType v = isSizeTypeTest <*> pure v

isSizeTypeTest :: TCM (Type -> Maybe BoundedSize)
isSizeTypeTest =
  flip (ifM (optSizedTypes <$> pragmaOptions)) (return $ const Nothing) $ do
    (size, sizelt) <- getBuiltinSize
    let testType (Def d [])  | Just d == size   = Just BoundedNo
        testType (Def d [v]) | Just d == sizelt = Just $ BoundedLt $ unArg v
        testType _                              = Nothing
    return $ testType . ignoreSharing . unEl

getBuiltinDefName :: String -> TCM (Maybe QName)
getBuiltinDefName s = fromDef . fmap ignoreSharing <$> getBuiltin' s
  where
    fromDef (Just (Def d [])) = Just d
    fromDef _                 = Nothing

getBuiltinSize :: TCM (Maybe QName, Maybe QName)
getBuiltinSize = do
  size   <- getBuiltinDefName builtinSize
  sizelt <- getBuiltinDefName builtinSizeLt
  return (size, sizelt)

isSizeNameTest :: TCM (QName -> Bool)
isSizeNameTest = ifM (optSizedTypes <$> pragmaOptions)
  isSizeNameTestRaw
  (return $ const False)

isSizeNameTestRaw :: TCM (QName -> Bool)
isSizeNameTestRaw = do
  (size, sizelt) <- getBuiltinSize
  return $ (`elem` [size, sizelt]) . Just

------------------------------------------------------------------------
-- * Constructors
------------------------------------------------------------------------

sizeType :: TCM Type
sizeType = El (mkType 0) <$> primSize

sizeSucName :: TCM (Maybe QName)
sizeSucName = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return Nothing) $ do
    Def x [] <- ignoreSharing <$> primSizeSuc
    return $ Just x
  `catchError` \_ -> return Nothing

sizeSuc :: Nat -> Term -> TCM Term
sizeSuc n v = do
  Def suc [] <- ignoreSharing <$> primSizeSuc
  return $ iterate (sizeSuc_ suc) v !! fromIntegral n

sizeSuc_ :: QName -> Term -> Term
sizeSuc_ suc v = Def suc [defaultArg v]

------------------------------------------------------------------------
-- * Viewing and unviewing sizes
------------------------------------------------------------------------

-- | A useful view on sizes.
data SizeView = SizeInf | SizeSuc Term | OtherSize Term

sizeView :: Term -> TCM SizeView
sizeView v = do
  Def inf [] <- ignoreSharing <$> primSizeInf
  Def suc [] <- ignoreSharing <$> primSizeSuc
  case ignoreSharing v of
    Def x []  | x == inf -> return SizeInf
    Def x [u] | x == suc -> return $ SizeSuc (unArg u)
    _                    -> return $ OtherSize v

type Offset = Nat

-- | A deep view on sizes.
data DeepSizeView
  = DSizeInf
  | DSizeVar Nat Offset
  | DSizeMeta MetaId Args Offset
  | DOtherSize Term

sizeViewSuc_ :: QName -> DeepSizeView -> DeepSizeView
sizeViewSuc_ suc v = case v of
  DSizeInf         -> DSizeInf
  DSizeVar i n     -> DSizeVar i (n + 1)
  DSizeMeta x vs n -> DSizeMeta x vs (n + 1)
  DOtherSize u     -> DOtherSize $ sizeSuc_ suc u

-- | @sizeViewPred k v@ decrements @v@ by @k@ (must be possible!).
sizeViewPred :: Nat -> DeepSizeView -> DeepSizeView
sizeViewPred 0 v = v
sizeViewPred k v = case v of
  DSizeInf -> DSizeInf
  DSizeVar  i    n | n >= k -> DSizeVar  i    (n - k)
  DSizeMeta x vs n | n >= k -> DSizeMeta x vs (n - k)
  _ -> __IMPOSSIBLE__

-- | @sizeViewOffset v@ returns the number of successors or Nothing when infty.
sizeViewOffset :: DeepSizeView -> Maybe Offset
sizeViewOffset v = case v of
  DSizeInf         -> Nothing
  DSizeVar i n     -> Just n
  DSizeMeta x vs n -> Just n
  DOtherSize u     -> Just 0

-- | Remove successors common to both sides.
removeSucs :: (DeepSizeView, DeepSizeView) -> (DeepSizeView, DeepSizeView)
removeSucs (v, w) = (sizeViewPred k v, sizeViewPred k w)
  where k = case (sizeViewOffset v, sizeViewOffset w) of
              (Just  n, Just  m) -> min n m
              (Just  n, Nothing) -> n
              (Nothing, Just  m) -> m
              (Nothing, Nothing) -> 0

-- | Turn a size view into a term.
unSizeView :: SizeView -> TCM Term
unSizeView SizeInf       = primSizeInf
unSizeView (SizeSuc v)   = sizeSuc 1 v
unSizeView (OtherSize v) = return v

unDeepSizeView :: DeepSizeView -> TCM Term
unDeepSizeView v = case v of
  DSizeInf         -> primSizeInf
  DSizeVar i     n -> sizeSuc n $ var i
  DSizeMeta x us n -> sizeSuc n $ MetaV x us
  DOtherSize u     -> return u
