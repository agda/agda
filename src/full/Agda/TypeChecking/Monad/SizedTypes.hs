{-# OPTIONS_GHC -Wunused-imports #-}

-- | Stuff for sized types that does not require modules
--   "Agda.TypeChecking.Reduce" or "Agda.TypeChecking.Constraints"
--   (which import "Agda.TypeChecking.Monad").

module Agda.TypeChecking.Monad.SizedTypes where

import Control.Monad.Except

import qualified Data.Foldable as Fold
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Polarity.Base
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Substitute

import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Syntax.Common.Pretty
import Agda.Utils.Singleton

import Agda.Utils.Impossible

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
class IsSizeType a where
  isSizeType :: (HasOptions m, HasBuiltins m) => a -> m (Maybe BoundedSize)

instance IsSizeType a => IsSizeType (Dom a) where
  isSizeType = isSizeType . unDom

instance IsSizeType a => IsSizeType (b,a) where
  isSizeType = isSizeType . snd

instance IsSizeType a => IsSizeType (Type' a) where
  isSizeType = isSizeType . unEl

instance IsSizeType Term where
  isSizeType v = isSizeTypeTest <*> pure v

instance IsSizeType CompareAs where
  isSizeType (AsTermsOf a) = isSizeType a
  isSizeType AsSizes       = return $ Just BoundedNo
  isSizeType AsTypes       = return Nothing

isSizeTypeTest :: (HasOptions m, HasBuiltins m) => m (Term -> Maybe BoundedSize)
isSizeTypeTest =
  flip (ifM sizedTypesOption) (return $ const Nothing) $ do
    (size, sizelt) <- getBuiltinSize
    let testType (Def d [])        | Just d == size   = Just BoundedNo
        testType (Def d [Apply v]) | Just d == sizelt = Just $ BoundedLt $ unArg v
        testType _                                    = Nothing
    return testType

getBuiltinDefName :: (HasBuiltins m) => BuiltinId -> m (Maybe QName)
getBuiltinDefName s = fromDef <$> getBuiltin' s
  where
    fromDef (Just (Def d [])) = Just d
    fromDef _                 = Nothing

getBuiltinSize :: (HasBuiltins m) => m (Maybe QName, Maybe QName)
getBuiltinSize = do
  size   <- getBuiltinDefName builtinSize
  sizelt <- getBuiltinDefName builtinSizeLt
  return (size, sizelt)

isSizeNameTest :: (HasOptions m, HasBuiltins m) => m (QName -> Bool)
isSizeNameTest = ifM sizedTypesOption
  isSizeNameTestRaw
  (return $ const False)

isSizeNameTestRaw :: (HasOptions m, HasBuiltins m) => m (QName -> Bool)
isSizeNameTestRaw = do
  (size, sizelt) <- getBuiltinSize
  return $ (`elem` [size, sizelt]) . Just

-- | Test whether OPTIONS --sized-types and whether
--   the size built-ins are defined.
haveSizedTypes :: TCM Bool
haveSizedTypes = do
    Def _ [] <- primSize
    Def _ [] <- primSizeInf
    Def _ [] <- primSizeSuc
    sizedTypesOption
  `catchError` \_ -> return False

-- | Test whether the SIZELT builtin is defined.
haveSizeLt :: TCM Bool
haveSizeLt = isJust <$> getBuiltinDefName builtinSizeLt

-- | Add polarity info to a SIZE builtin.
builtinSizeHook :: BuiltinId -> QName -> Type -> TCM ()
builtinSizeHook s q t = do
  when (s `elem` [builtinSizeLt, builtinSizeSuc]) $ do
    modifySignature $ updateDefinition q
      $ updateDefPolarity       (const [Covariant])
      . updateDefArgOccurrences (const [StrictPos])
  when (s == builtinSizeMax) $ do
    modifySignature $ updateDefinition q
      $ updateDefPolarity       (const [Covariant, Covariant])
      . updateDefArgOccurrences (const [StrictPos, StrictPos])
{-
      . updateDefType           (const tmax)
  where
    -- TODO: max : (i j : Size) -> Size< (suc (max i j))
    tmax =
-}

------------------------------------------------------------------------
-- * Constructors
------------------------------------------------------------------------

-- | The sort of built-in types @SIZE@ and @SIZELT@.
sizeSort :: Sort
sizeSort = mkType 0

-- | The type of built-in types @SIZE@ and @SIZELT@.
sizeUniv :: Type
sizeUniv = sort $ sizeSort

-- | The built-in type @SIZE@ with user-given name.
sizeType_ :: QName -> Type
sizeType_ size = El sizeSort $ Def size []

{-# SPECIALIZE sizeType :: TCM Type #-}
-- | The built-in type @SIZE@.
sizeType :: (HasBuiltins m, MonadTCEnv m, ReadTCState m) => m Type
sizeType = El sizeSort . fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSize

-- | The name of @SIZESUC@.
sizeSucName :: (HasBuiltins m, HasOptions m) => m (Maybe QName)
sizeSucName = do
  ifM (not <$> sizedTypesOption) (return Nothing) $ do
    getBuiltin' builtinSizeSuc >>= \case
      Just (Def x []) -> return $ Just x
      _               -> return Nothing

{-# SPECIALIZE sizeSuc :: Nat -> Term -> TCM Term #-}
sizeSuc :: HasBuiltins m => Nat -> Term -> m Term
sizeSuc n v | n < 0     = __IMPOSSIBLE__
            | n == 0    = return v
            | otherwise = do
  Def suc [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSizeSuc
  return $ fromMaybe __IMPOSSIBLE__ (iterate (sizeSuc_ suc) v !!! n)

sizeSuc_ :: QName -> Term -> Term
sizeSuc_ suc v = Def suc [Apply $ defaultArg v]

-- | Transform list of terms into a term build from binary maximum.
sizeMax :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
        => List1 Term -> m Term
sizeMax vs = case vs of
  v :| [] -> return v
  vs  -> do
    Def max [] <- primSizeMax
    return $ foldr1 (\ u v -> Def max $ map (Apply . defaultArg) [u,v]) vs


------------------------------------------------------------------------
-- * Viewing and unviewing sizes
------------------------------------------------------------------------

-- | A useful view on sizes.
data SizeView = SizeInf | SizeSuc Term | OtherSize Term

-- | Expects argument to be 'reduce'd.
sizeView :: (HasBuiltins m, MonadTCEnv m, ReadTCState m)
         => Term -> m SizeView
sizeView v = do
  Def inf [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSizeInf
  Def suc [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSizeSuc
  case v of
    Def x []        | x == inf -> return SizeInf
    Def x [Apply u] | x == suc -> return $ SizeSuc (unArg u)
    _                          -> return $ OtherSize v

-- | A de Bruijn index under some projections.

data ProjectedVar = ProjectedVar
  { pvIndex :: Int
  , prProjs :: [(ProjOrigin, QName)]
  }
  deriving (Show)

-- | Ignore 'ProjOrigin' in equality test.

instance Eq ProjectedVar where
  ProjectedVar i prjs == ProjectedVar i' prjs' =
    i == i' && map snd prjs == map snd prjs'

viewProjectedVar :: Term -> Maybe ProjectedVar
viewProjectedVar = \case
  Var i es -> ProjectedVar i <$> mapM isProjElim es
  _ -> Nothing

unviewProjectedVar :: ProjectedVar -> Term
unviewProjectedVar (ProjectedVar i prjs) = Var i $ map (uncurry Proj) prjs

type Offset = Nat

-- | A deep view on sizes.
data DeepSizeView
  = DSizeInf
  | DSizeVar ProjectedVar Offset
  | DSizeMeta MetaId Elims Offset
  | DOtherSize Term
  deriving (Show)

instance Pretty DeepSizeView where
  pretty = \case
    DSizeInf        -> "∞"
    DSizeVar pv o    -> pretty (unviewProjectedVar pv) <+> "+" <+> pretty o
    DSizeMeta x es o -> pretty (MetaV x es) <+> "+" <+> pretty o
    DOtherSize t     -> pretty t

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
sizeViewSuc_ suc = \case
  DSizeInf         -> DSizeInf
  DSizeVar i n     -> DSizeVar i (n + 1)
  DSizeMeta x vs n -> DSizeMeta x vs (n + 1)
  DOtherSize u     -> DOtherSize $ sizeSuc_ suc u

-- | @sizeViewPred k v@ decrements @v@ by @k@ (must be possible!).
sizeViewPred :: Nat -> DeepSizeView -> DeepSizeView
sizeViewPred 0 = id
sizeViewPred k = \case
  DSizeInf -> DSizeInf
  DSizeVar  i    n | n >= k -> DSizeVar  i    (n - k)
  DSizeMeta x vs n | n >= k -> DSizeMeta x vs (n - k)
  _ -> __IMPOSSIBLE__

-- | @sizeViewOffset v@ returns the number of successors or Nothing when infty.
sizeViewOffset :: DeepSizeView -> Maybe Offset
sizeViewOffset = \case
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

unDeepSizeView :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
               => DeepSizeView -> m Term
unDeepSizeView = \case
  DSizeInf         -> primSizeInf
  DSizeVar pv    n -> sizeSuc n $ unviewProjectedVar pv
  DSizeMeta x us n -> sizeSuc n $ MetaV x us
  DOtherSize u     -> return u

------------------------------------------------------------------------
-- * View on sizes where maximum is pulled to the top
------------------------------------------------------------------------

type SizeMaxView = List1 DeepSizeView
type SizeMaxView' = [DeepSizeView]

maxViewMax :: SizeMaxView -> SizeMaxView -> SizeMaxView
maxViewMax v w = case (v,w) of
  (DSizeInf :| _, _) -> singleton DSizeInf
  (_, DSizeInf :| _) -> singleton DSizeInf
  _                 -> Fold.foldr maxViewCons w v

-- | @maxViewCons v ws = max v ws@.  It only adds @v@ to @ws@ if it is not
--   subsumed by an element of @ws@.
maxViewCons :: DeepSizeView -> SizeMaxView -> SizeMaxView
maxViewCons _ (DSizeInf :| _) = singleton DSizeInf
maxViewCons DSizeInf _        = singleton DSizeInf
maxViewCons v ws = case sizeViewComparableWithMax v ws of
  NotComparable  -> List1.cons v ws
  YesAbove _ ws' -> v :| ws'
  YesBelow{}     -> ws

-- | @sizeViewComparableWithMax v ws@ tries to find @w@ in @ws@ that compares with @v@
--   and singles this out.
--   Precondition: @v /= DSizeInv@.
sizeViewComparableWithMax :: DeepSizeView -> SizeMaxView -> SizeViewComparable SizeMaxView'
sizeViewComparableWithMax v (w :| ws) =
  case (ws, sizeViewComparable v w) of
    (w':ws', NotComparable) -> (w:) <$> sizeViewComparableWithMax v (w' :| ws')
    (ws    , r)             -> fmap (const ws) r


maxViewSuc_ :: QName -> SizeMaxView -> SizeMaxView
maxViewSuc_ suc = fmap (sizeViewSuc_ suc)

unMaxView :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
          => SizeMaxView -> m Term
unMaxView vs = sizeMax =<< Trav.mapM unDeepSizeView vs
