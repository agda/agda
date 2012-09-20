{-# LANGUAGE CPP #-}
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
-- * Handling of size builtins
------------------------------------------------------------------------

-- | Check if a type is the 'primSize' type. The argument should be 'reduce'd.

isSizeType :: Type -> TCM Bool
isSizeType v = isSizeTypeTest <*> pure v

{- ORIGINAL CODE
isSizeType :: Type -> TCM Bool
isSizeType (El _ v) = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return False) $
  case v of
    Def x [] -> do
      Def size [] <- primSize
      return $ x == size
    _ -> return False
  `catchError` \_ -> return False

isSizeNameTest :: TCM (QName -> Bool)
isSizeNameTest = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return $ const False) $ do
    Def size [] <- primSize
    return (size ==)
  `catchError` \_ -> return $ const False
-}

isSizeNameTest :: TCM (QName -> Bool)
isSizeNameTest = ifM (optSizedTypes <$> pragmaOptions)
  isSizeNameTestRaw
  (return $ const False)

isSizeNameTestRaw :: TCM (QName -> Bool)
isSizeNameTestRaw = liftTCM $
  do
    Def size [] <- primSize
    return (size ==)
  `catchError` \_ -> return $ const False

isSizeTypeTest :: TCM (Type -> Bool)
isSizeTypeTest =
  ifM (not . optSizedTypes <$> pragmaOptions) (return $ const False) $ do
    testName <- isSizeNameTestRaw
    let testType (El _ (Def d [])) = testName d
        testType _                 = False
    return testType

sizeType :: TCM Type
sizeType = El (mkType 0) <$> primSize

sizeSucName :: TCM (Maybe QName)
sizeSucName = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return Nothing) $ do
    Def x [] <- primSizeSuc
    return $ Just x
  `catchError` \_ -> return Nothing

------------------------------------------------------------------------
-- * Viewing and unviewing sizes
------------------------------------------------------------------------

-- | A useful view on sizes.
data SizeView = SizeInf | SizeSuc Term | OtherSize Term

sizeView :: Term -> TCM SizeView
sizeView v = do
  Def inf [] <- primSizeInf
  Def suc [] <- primSizeSuc
  case v of
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

sizeSuc :: Nat -> Term -> TCM Term
sizeSuc n v = do
  Def suc [] <- primSizeSuc
  return $ iterate (sizeSuc_ suc) v !! fromIntegral n

sizeSuc_ :: QName -> Term -> Term
sizeSuc_ suc v = Def suc [defaultArg v]
