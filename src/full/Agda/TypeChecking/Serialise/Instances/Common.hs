{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}

module Agda.TypeChecking.Serialise.Instances.Common (SerialisedRange(..)) where

import Control.Monad              ( (<=<) )
import Control.Monad.IO.Class     ( MonadIO(..) )
import Control.Monad.Except       ( MonadError(..) )
import Control.Monad.Reader       ( MonadReader(..), asks )
import Control.Monad.State.Strict ( gets, modify )

import Data.Array.IArray
import Data.Word
import qualified Data.Foldable as Fold
import Data.Hashable
import Data.Int (Int32)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Strict.Tuple (Pair(..))
import qualified Data.Text      as T
import qualified Data.Text.Lazy as TL
import Data.Typeable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap

import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Builtin
import Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Position as P
import Agda.Syntax.Literal
import Agda.Syntax.TopLevelModuleName
import Agda.Interaction.FindFile
import Agda.Interaction.Library

import Agda.TypeChecking.Serialise.Base

import Agda.Utils.BiMap (BiMap)
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.List2 (List2(List2))
import qualified Agda.Utils.List2 as List2
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Trie (Trie(..))
import Agda.Utils.WithDefault

import Agda.Utils.Impossible
import Agda.Utils.CallStack

instance {-# OVERLAPPING #-} EmbPrj String where
  icod_   = icodeString
  value i = (! i) `fmap` gets stringE

instance EmbPrj TL.Text where
  icod_   = icodeX lTextD lTextC
  value i = (! i) `fmap` gets lTextE

instance EmbPrj T.Text where
  icod_   = icodeX sTextD sTextC
  value i = (! i) `fmap` gets sTextE

instance EmbPrj Integer where
  icod_   = icodeInteger
  value i = (! i) `fmap` gets integerE

instance EmbPrj Word64 where
  icod_ i = icodeN' (undefined :: Int32 -> Int32 -> Int32) (int32 q) (int32 r)
    where (q, r) = quotRem i (2^32)
          int32 :: Word64 -> Int32
          int32 = fromIntegral

  value = vcase valu where
    valu [a, b] = return $ n * mod (fromIntegral a) n + mod (fromIntegral b) n
    valu _      = malformed
    n = 2^32

instance EmbPrj Int32 where
  icod_ i = return i
  value i = return i

instance EmbPrj Int where
  icod_ i = return (fromIntegral i)
  value i = return (fromIntegral i)

instance EmbPrj Char where
  icod_ c = return (fromIntegral $ fromEnum c)
  value i = return (toEnum $ fromInteger $ toInteger i)

instance EmbPrj Double where
  icod_   = icodeDouble
  value i = (! i) `fmap` gets doubleE

instance EmbPrj Void where
  icod_ = absurd
  value = vcase valu where valu _ = malformed

instance EmbPrj () where
  icod_ () = pure 0

  value 0 = pure ()
  value _ = malformed

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icod_ (a, b) = icodeN' (,) a b

  value = valueN (,)

instance (EmbPrj a, EmbPrj b) => EmbPrj (Pair a b) where
  icod_ (a :!: b) = icodeN' (:!:) a b

  value = valueN (:!:)

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icod_ (a, b, c) = icodeN' (,,) a b c

  value = valueN (,,)

instance (EmbPrj a, EmbPrj b) => EmbPrj (Either a b) where
  icod_ (Left  x) = icodeN 0 Left x
  icod_ (Right x) = icodeN 1 Right x

  value = vcase valu where
    valu [0, x] = valuN Left  x
    valu [1, x] = valuN Right x
    valu _   = malformed

instance EmbPrj a => EmbPrj (Maybe a) where
  icod_ Nothing  = icodeN' Nothing
  icod_ (Just x) = icodeN' Just x

  value = vcase valu where
    valu []  = valuN Nothing
    valu [x] = valuN Just x
    valu _   = malformed

instance EmbPrj a => EmbPrj (Strict.Maybe a) where
  icod_ m = icode (Strict.toLazy m)
  value m = Strict.toStrict `fmap` value m

instance EmbPrj Bool where
  icod_ False = pure 0
  icod_ True  = pure 1

  value 0 = pure False
  value 1 = pure True
  value _ = malformed

instance EmbPrj FileType where
  icod_ AgdaFileType  = pure 0
  icod_ MdFileType    = pure 1
  icod_ RstFileType   = pure 2
  icod_ TexFileType   = pure 3
  icod_ OrgFileType   = pure 4
  icod_ TypstFileType = pure 5

  value = \case
    0 -> pure AgdaFileType
    1 -> pure MdFileType
    2 -> pure RstFileType
    3 -> pure TexFileType
    4 -> pure OrgFileType
    5 -> pure TypstFileType
    _ -> malformed

instance EmbPrj Cubical where
  icod_ CErased = icodeN'  CErased
  icod_ CFull   = icodeN 0 CFull

  value = vcase $ \case
    []  -> valuN CErased
    [0] -> valuN CFull
    _   -> malformed

instance EmbPrj Language where
  icod_ WithoutK    = icodeN'  WithoutK
  icod_ WithK       = icodeN 0 WithK
  icod_ (Cubical a) = icodeN 1 Cubical a

  value = vcase $ \case
    []     -> valuN WithoutK
    [0]    -> valuN WithK
    [1, a] -> valuN Cubical a
    _      -> malformed

instance EmbPrj a => EmbPrj (Position' a) where
  icod_ (P.Pn file pos line col) = icodeN' P.Pn file pos line col

  value = valueN P.Pn

instance (EmbPrj a, Typeable b) => EmbPrj (WithDefault' a b) where
  icod_ = \case
    Default -> icodeN' Default
    Value b -> icodeN' Value b

  value = vcase $ \case
    []  -> valuN Default
    [a] -> valuN Value a
    _ -> malformed

instance EmbPrj TopLevelModuleName where
  icod_ (TopLevelModuleName a b c) = icodeN' TopLevelModuleName a b c

  value = valueN TopLevelModuleName

instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
  icod_ xs = icodeNode =<< mapM icode xs
  value    = vcase (mapM value)
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = malformed

instance EmbPrj a => EmbPrj (List1 a) where
  icod_ = icod_ . List1.toList
  value = maybe malformed return . List1.nonEmpty <=< value

instance EmbPrj a => EmbPrj (List2 a) where
  icod_ = icod_ . List2.toList
  value = maybe malformed return . List2.fromListMaybe <=< value

instance (EmbPrj k, EmbPrj v, EmbPrj (BiMap.Tag v)) =>
         EmbPrj (BiMap k v) where
  icod_ m = icode (BiMap.toDistinctAscendingLists m)
  value m = BiMap.fromDistinctAscendingLists <$> value m


-- | Encode a list of key-value pairs as a flat list.
mapPairsIcode :: (EmbPrj k, EmbPrj v) => [(k, v)] -> S Int32
mapPairsIcode xs = icodeNode =<< convert [] xs where
  -- As we need to call `convert' in the tail position, the resulting list is
  -- written (and read) in reverse order, with the highest pair first in the
  -- resulting list.
  convert ys [] = return ys
  convert ys ((start, entry):xs) = do
    start <- icode start
    entry <- icode entry
    convert (start:entry:ys) xs

mapPairsValue :: (EmbPrj k, EmbPrj v) => [Int32] -> R [(k, v)]
mapPairsValue = convert [] where
  convert ys [] = return ys
  convert ys (start:entry:xs) = do
    start <- value start
    entry <- value entry
    convert ((start, entry):ys) xs
  convert _ _ = malformed

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icod_ m = mapPairsIcode (Map.toAscList m)
  value = vcase (fmap Map.fromDistinctAscList . mapPairsValue)

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icod_ s = icode (Set.toAscList s)
  value s = Set.fromDistinctAscList <$> value s

instance EmbPrj IntSet where
  icod_ s = icode (IntSet.toAscList s)
  value s = IntSet.fromDistinctAscList <$> value s

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Trie a b) where
  icod_ (Trie a b)= icodeN' Trie a b

  value = valueN Trie

instance EmbPrj a => EmbPrj (Seq a) where
  icod_ s = icode (Fold.toList s)
  value s = Seq.fromList `fmap` value s

instance EmbPrj a => EmbPrj (P.Interval' a) where
  icod_ (P.Interval p q) = icodeN' P.Interval p q

  value = valueN P.Interval

instance EmbPrj RangeFile where
  icod_ (RangeFile _ Nothing)  = __IMPOSSIBLE__
  icod_ (RangeFile _ (Just a)) = icode a

  value r = do
    m :: TopLevelModuleName
            <- value r
    mf      <- gets modFile
    incs    <- gets includes
    (r, mf) <- liftIO $ findFile'' incs m mf
    modify $ \s -> s { modFile = mf }
    case r of
      Left err -> throwError $ findErrorToTypeError m err
      Right f  -> return $ RangeFile (srcFilePath f) (Just m)

-- | Ranges are always deserialised as 'noRange'.

instance EmbPrj Range where
  icod_ _ = icodeN' ()
  value _ = return noRange

-- | Ranges that should be serialised properly.

newtype SerialisedRange = SerialisedRange { underlyingRange :: Range }

instance EmbPrj SerialisedRange where
  icod_ (SerialisedRange r) = icodeN' P.intervalsToRange (P.rangeFile r) (P.rangeIntervals r)

  value i = SerialisedRange <$> valueN P.intervalsToRange i

instance EmbPrj C.Name where
  icod_ (C.NoName a b)     = icodeN 0 C.NoName a b
  icod_ (C.Name r nis xs)  = icodeN 1 C.Name r nis xs

  value = vcase valu where
    valu [0, a, b]       = valuN C.NoName a b
    valu [1, r, nis, xs] = valuN C.Name   r nis xs
    valu _               = malformed

instance EmbPrj NamePart where
  icod_ Hole   = icodeN' Hole
  icod_ (Id a) = icodeN' Id a

  value = vcase valu where
    valu []  = valuN Hole
    valu [a] = valuN Id a
    valu _   = malformed

instance EmbPrj NameInScope where
  icod_ InScope    = icodeN' InScope
  icod_ NotInScope = icodeN 0 NotInScope

  value = vcase valu where
    valu []  = valuN InScope
    valu [0] = valuN NotInScope
    valu _   = malformed

instance EmbPrj C.QName where
  icod_ (Qual    a b) = icodeN' Qual a b
  icod_ (C.QName a  ) = icodeN' C.QName a

  value = vcase valu where
    valu [a, b] = valuN Qual    a b
    valu [a]    = valuN C.QName a
    valu _      = malformed

instance (EmbPrj a, EmbPrj b) => EmbPrj (ImportedName' a b) where
  icod_ (ImportedModule a) = icodeN 1 ImportedModule a
  icod_ (ImportedName a)   = icodeN 2 ImportedName a

  value = vcase valu where
    valu [1, a] = valuN ImportedModule a
    valu [2, a] = valuN ImportedName a
    valu _ = malformed

instance EmbPrj Associativity where
  icod_ LeftAssoc  = pure 0
  icod_ RightAssoc = pure 1
  icod_ NonAssoc   = pure 2

  value = \case
    0 -> pure LeftAssoc
    1 -> pure RightAssoc
    2 -> pure NonAssoc
    _ -> malformed

instance EmbPrj FixityLevel where
  icod_ Unrelated   = icodeN' Unrelated
  icod_ (Related a) = icodeN' Related a

  value = vcase valu where
    valu []  = valuN Unrelated
    valu [a] = valuN Related a
    valu _   = malformed

instance EmbPrj Fixity where
  icod_ (Fixity a b c) = icodeN' Fixity a b c

  value = valueN Fixity

instance EmbPrj Fixity' where
  icod_ (Fixity' a b r) = icodeN' (\ a b -> Fixity' a b r) a b  -- discard theNameRange

  value = valueN (\ f n -> Fixity' f n noRange)

instance EmbPrj BoundVariablePosition where
  icod_ (BoundVariablePosition a b) = icodeN' BoundVariablePosition a b

  value = valueN BoundVariablePosition

instance EmbPrj NotationPart where
  icod_ (VarPart a b)  = icodeN 0 VarPart a b
  icod_ (HolePart a b) = icodeN 1 HolePart a b
  icod_ (WildPart a)   = icodeN 2 WildPart a
  icod_ (IdPart a)     = icodeN' IdPart a

  value = vcase valu where
    valu [0, a, b] = valuN VarPart a b
    valu [1, a, b] = valuN HolePart a b
    valu [2, a]    = valuN WildPart a
    valu [a]       = valuN IdPart a
    valu _         = malformed

instance EmbPrj MetaId where
  icod_ (MetaId a b) = icode (a, b)

  value m = uncurry MetaId <$> value m

instance EmbPrj A.QName where
  icod_ n@(A.QName a b) = icodeMemo qnameD qnameC (qnameId n) $ icodeN' A.QName a b

  value = valueN A.QName

instance EmbPrj A.AmbiguousQName where
  icod_ (A.AmbQ a) = icode a
  value n          = A.AmbQ `fmap` value n

instance EmbPrj A.ModuleName where
  icod_ (A.MName a) = icode a
  value n           = A.MName `fmap` value n

instance EmbPrj A.Name where
  icod_ (A.Name a b c d e f) = icodeMemo nameD nameC a $
    icodeN' (\ a b c -> A.Name a b c . underlyingRange) a b c (SerialisedRange d) e f

  value = valueN (\a b c d -> A.Name a b c (underlyingRange d))

instance EmbPrj a => EmbPrj (C.FieldAssignment' a) where
  icod_ (C.FieldAssignment a b) = icodeN' C.FieldAssignment a b

  value = valueN C.FieldAssignment

instance (EmbPrj s, EmbPrj t) => EmbPrj (Named s t) where
  icod_ (Named a b) = icodeN' Named a b

  value = valueN Named

instance EmbPrj a => EmbPrj (Ranged a) where
  icod_ (Ranged r x) = icodeN' Ranged r x

  value = valueN Ranged

instance EmbPrj ArgInfo where
  icod_ (ArgInfo h r o fv ann) = icodeN' ArgInfo h r o fv ann

  value = valueN ArgInfo

instance EmbPrj ModuleNameHash where
  icod_ (ModuleNameHash a) = icodeN' ModuleNameHash a

  value = valueN ModuleNameHash

instance EmbPrj NameId where
  icod_ (NameId a b) = icodeN' NameId a b

  value = valueN NameId

instance EmbPrj OpaqueId where
  icod_ (OpaqueId a b) = icodeN' OpaqueId a b

  value = valueN OpaqueId

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icod_ m = mapPairsIcode (HMap.toList m)
  value = vcase (fmap HMap.fromList . mapPairsValue)

instance EmbPrj a => EmbPrj (WithHiding a) where
  icod_ (WithHiding a b) = icodeN' WithHiding a b

  value = valueN WithHiding

instance EmbPrj a => EmbPrj (Arg a) where
  icod_ (Arg i e) = icodeN' Arg i e

  value = valueN Arg

instance EmbPrj a => EmbPrj (HasEta' a) where
  icod_ YesEta    = icodeN' YesEta
  icod_ (NoEta a) = icodeN' NoEta a

  value = vcase valu where
    valu []  = valuN YesEta
    valu [a] = valuN NoEta a
    valu _   = malformed

instance EmbPrj PatternOrCopattern

instance EmbPrj Induction where
  icod_ Inductive   = icodeN' Inductive
  icod_ CoInductive = icodeN 1 CoInductive

  value = vcase valu where
    valu []  = valuN Inductive
    valu [1] = valuN CoInductive
    valu _   = malformed

instance EmbPrj Hiding where
  icod_ Hidden                = return 0
  icod_ NotHidden             = return 1
  icod_ (Instance NoOverlap)  = return 2
  icod_ (Instance YesOverlap) = return 3

  value 0 = return Hidden
  value 1 = return NotHidden
  value 2 = return (Instance NoOverlap)
  value 3 = return (Instance YesOverlap)
  value _ = malformed

instance EmbPrj Q0Origin where
  icod_ = \case
    Q0Inferred -> return 0
    Q0 _       -> return 1
    Q0Erased _ -> return 2

  value = \case
    0 -> return $ Q0Inferred
    1 -> return $ Q0       noRange
    2 -> return $ Q0Erased noRange
    _ -> malformed

instance EmbPrj Q1Origin where
  icod_ = \case
    Q1Inferred -> return 0
    Q1 _       -> return 1
    Q1Linear _ -> return 2

  value = \case
    0 -> return $ Q1Inferred
    1 -> return $ Q1       noRange
    2 -> return $ Q1Linear noRange
    _ -> malformed

instance EmbPrj QωOrigin where
  icod_ = \case
    QωInferred -> return 0
    Qω _       -> return 1
    QωPlenty _ -> return 2

  value = \case
    0 -> return $ QωInferred
    1 -> return $ Qω       noRange
    2 -> return $ QωPlenty noRange
    _ -> malformed

instance EmbPrj Quantity where
  icod_ = \case
    Quantity0 a -> icodeN 0 Quantity0 a
    Quantity1 a -> icodeN 1 Quantity1 a
    Quantityω a -> icodeN'  Quantityω a  -- default quantity, shorter code

  value = vcase $ \case
    [0, a] -> valuN Quantity0 a
    [1, a] -> valuN Quantity1 a
    [a]    -> valuN Quantityω a
    _      -> malformed

-- -- ALT: forget quantity origin when serializing?
-- instance EmbPrj Quantity where
--   icod_ Quantity0 = return 0
--   icod_ Quantity1 = return 1
--   icod_ Quantityω = return 2

--   value 0 = return Quantity0
--   value 1 = return Quantity1
--   value 2 = return Quantityω
--   value _ = malformed

instance EmbPrj Cohesion where
  icod_ Flat       = return 0
  icod_ Continuous = return 1
  icod_ Squash     = return 2

  value 0 = return Flat
  value 1 = return Continuous
  value 2 = return Squash
  value _ = malformed

instance EmbPrj Modality where
  icod_ (Modality a b c) = icodeN' Modality a b c

  value = vcase $ \case
    [a, b, c] -> valuN Modality a b c
    _ -> malformed

instance EmbPrj Relevance where
  icod_ Relevant       = return 0
  icod_ Irrelevant     = return 1
  icod_ NonStrict      = return 2

  value 0 = return Relevant
  value 1 = return Irrelevant
  value 2 = return NonStrict
  value _ = malformed

instance EmbPrj Annotation where
  icod_ (Annotation l) = icodeN' Annotation l

  value = valueN Annotation

instance EmbPrj Lock where
  icod_ IsNotLock          = pure 0
  icod_ (IsLock LockOTick) = pure 1
  icod_ (IsLock LockOLock) = pure 2

  value 0 = pure IsNotLock
  value 1 = pure (IsLock LockOTick)
  value 2 = pure (IsLock LockOLock)
  value _ = malformed

instance EmbPrj Origin where
  icod_ UserWritten = return 0
  icod_ Inserted    = return 1
  icod_ Reflected   = return 2
  icod_ CaseSplit   = return 3
  icod_ Substitution = return 4
  icod_ ExpandedPun = return 5
  icod_ Generalization = return 6

  value 0 = return UserWritten
  value 1 = return Inserted
  value 2 = return Reflected
  value 3 = return CaseSplit
  value 4 = return Substitution
  value 5 = return ExpandedPun
  value 6 = return Generalization
  value _ = malformed

instance EmbPrj a => EmbPrj (WithOrigin a) where
  icod_ (WithOrigin a b) = icodeN' WithOrigin a b

  value = valueN WithOrigin

instance EmbPrj FreeVariables where
  icod_ UnknownFVs   = icodeN' UnknownFVs
  icod_ (KnownFVs a) = icodeN' KnownFVs a

  value = vcase valu where
    valu []  = valuN UnknownFVs
    valu [a] = valuN KnownFVs a
    valu _   = malformed

instance EmbPrj ConOrigin where
  icod_ ConOSystem = return 0
  icod_ ConOCon    = return 1
  icod_ ConORec    = return 2
  icod_ ConOSplit  = return 3

  value 0 = return ConOSystem
  value 1 = return ConOCon
  value 2 = return ConORec
  value 3 = return ConOSplit
  value _ = malformed

instance EmbPrj ProjOrigin where
  icod_ ProjPrefix  = return 0
  icod_ ProjPostfix = return 1
  icod_ ProjSystem  = return 2

  value 0 = return ProjPrefix
  value 1 = return ProjPostfix
  value 2 = return ProjSystem
  value _ = malformed

instance EmbPrj Agda.Syntax.Literal.Literal where
  icod_ (LitNat    a)   = icodeN' LitNat a
  icod_ (LitFloat  a)   = icodeN 1 LitFloat a
  icod_ (LitString a)   = icodeN 2 LitString a
  icod_ (LitChar   a)   = icodeN 3 LitChar a
  icod_ (LitQName  a)   = icodeN 5 LitQName a
  icod_ (LitMeta   a b) = icodeN 6 LitMeta a b
  icod_ (LitWord64 a)   = icodeN 7 LitWord64 a

  value = vcase valu where
    valu [a]       = valuN LitNat    a
    valu [1, a]    = valuN LitFloat  a
    valu [2, a]    = valuN LitString a
    valu [3, a]    = valuN LitChar   a
    valu [5, a]    = valuN LitQName  a
    valu [6, a, b] = valuN LitMeta   a b
    valu [7, a]    = valuN LitWord64 a
    valu _            = malformed

instance EmbPrj IsAbstract where
  icod_ AbstractDef = icodeN 0 AbstractDef
  icod_ ConcreteDef = icodeN' ConcreteDef

  value = vcase valu where
    valu [0] = valuN AbstractDef
    valu []  = valuN ConcreteDef
    valu _   = malformed

instance EmbPrj IsOpaque where
  icod_ (OpaqueDef a)  = icodeN' OpaqueDef a
  icod_ TransparentDef = icodeN' TransparentDef

  value = vcase valu where
    valu [a] = valuN OpaqueDef a
    valu []  = valuN TransparentDef
    valu _   = malformed

instance EmbPrj SrcLoc where
  icod_ (SrcLoc p m f sl sc el ec) = icodeN' SrcLoc p m f sl sc el ec
  value = valueN SrcLoc

instance EmbPrj CallStack where
  icod_ = icode . getCallStack
  value = fmap fromCallSiteList . value

instance EmbPrj Impossible where
  icod_ (Impossible a)              = icodeN 0 Impossible a
  icod_ (Unreachable a)             = icodeN 1 Unreachable a
  icod_ (ImpMissingDefinitions a b) = icodeN 2 ImpMissingDefinitions a b

  value = vcase valu where
    valu [0, a]    = valuN Impossible  a
    valu [1, a]    = valuN Unreachable a
    valu [2, a, b] = valuN ImpMissingDefinitions a b
    valu _         = malformed

instance EmbPrj ExpandedEllipsis where
  icod_ NoEllipsis = icodeN' NoEllipsis
  icod_ (ExpandedEllipsis a b) = icodeN 1 ExpandedEllipsis a b

  value = vcase valu where
    valu []      = valuN NoEllipsis
    valu [1,a,b] = valuN ExpandedEllipsis a b
    valu _       = malformed

instance EmbPrj OptionsPragma where
  icod_ (OptionsPragma a b) = icod_ (a, b)

  value op = uncurry OptionsPragma <$> value op

instance EmbPrj BuiltinId
instance EmbPrj PrimitiveId

instance EmbPrj SomeBuiltin where
  icod_ (BuiltinName x)   = icodeN 0 BuiltinName x
  icod_ (PrimitiveName x) = icodeN 1 PrimitiveName x

  value = vcase valu where
    valu [0, x] = valuN BuiltinName x
    valu [1, x] = valuN PrimitiveName x
    valu _      = malformed
