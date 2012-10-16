{-# LANGUAGE CPP, TupleSections, DeriveFunctor #-}
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
  return $ iterate (sizeSuc_ suc) v !! n

sizeSuc_ :: QName -> Term -> Term
sizeSuc_ suc v = Def suc [defaultArg v]

-- | Transform list of terms into a term build from binary maximum.
sizeMax :: [Term] -> TCM Term
sizeMax vs = case vs of
  []  -> __IMPOSSIBLE__  -- we do not have a zero size
  [v] -> return v
  vs  -> do
    Def max [] <- primSizeMax
    return $ foldr1 (\ u v -> Def max $ map defaultArg [u,v]) vs


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

data SizeViewComparable a
  = NotComparable
  | YesAbove DeepSizeView a
  | YesBelow DeepSizeView a
  deriving (Functor)

-- | @sizeViewComparable v w@ checks whether @v >= w@ (then @Left@)
--   or @v <= w@ (then @Right@).  If uncomparable, it returns @NotComparable@.
sizeViewComparable :: DeepSizeView -> DeepSizeView -> SizeViewComparable ()
sizeViewComparable v w = case (v,w) of
  (DSizeInf, _) -> YesAbove w ()
  (_, DSizeInf) -> YesBelow w ()
  (DSizeVar x n, DSizeVar y m) | x == y -> if n >= m then YesAbove w () else YesBelow w ()
  _ -> NotComparable

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

------------------------------------------------------------------------
-- * View on sizes where maximum is pulled to the top
------------------------------------------------------------------------

type SizeMaxView = [DeepSizeView]

maxViewMax :: SizeMaxView -> SizeMaxView -> SizeMaxView
maxViewMax v w = case (v,w) of
  (DSizeInf : _, _) -> [DSizeInf]
  (_, DSizeInf : _) -> [DSizeInf]
  _                 -> foldr maxViewCons w v

-- | @maxViewCons v ws = max v ws@.  It only adds @v@ to @ws@ if it is not
--   subsumed by an element of @ws@.
maxViewCons :: DeepSizeView -> SizeMaxView -> SizeMaxView
maxViewCons _ [DSizeInf] = [DSizeInf]
maxViewCons DSizeInf _   = [DSizeInf]
maxViewCons v ws = case sizeViewComparableWithMax v ws of
  NotComparable  -> v:ws
  YesAbove _ ws' -> v:ws'
  YesBelow{}     -> ws

-- | @sizeViewComparableWithMax v ws@ tries to find @w@ in @ws@ that compares with @v@
--   and singles this out.
--   Precondition: @v /= DSizeInv@.
sizeViewComparableWithMax :: DeepSizeView -> SizeMaxView -> SizeViewComparable SizeMaxView
sizeViewComparableWithMax v ws = case ws of
  []     -> __IMPOSSIBLE__
  [w]    -> fmap (const []) $ sizeViewComparable v w
  (w:ws) -> case sizeViewComparable v w of
            NotComparable -> fmap (w:) $ sizeViewComparableWithMax v ws
            r  -> fmap (const ws) r


maxViewSuc_ :: QName -> SizeMaxView -> SizeMaxView
maxViewSuc_ suc = map (sizeViewSuc_ suc)

unMaxView :: SizeMaxView -> TCM Term
unMaxView vs = sizeMax =<< mapM unDeepSizeView vs
