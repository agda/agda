
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Common (SerialisedRange(..)) where

import Prelude hiding (mapM)

import Control.Monad.Reader hiding (mapM)
import Control.Monad.State.Strict (gets, modify)


import Data.Array.IArray
import Data.Word
import qualified Data.Foldable as Fold
import Data.Hashable
import qualified Data.HashTable.IO as H
import Data.Int (Int32)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text.Lazy (Text)
import Data.Traversable ( mapM )
import Data.Typeable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap

import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Position as P
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal
import Agda.Interaction.FindFile

import Agda.TypeChecking.Serialise.Base

import Agda.Utils.BiMap (BiMap)
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.FileName
import Agda.Utils.Maybe
import Agda.Utils.NonemptyList
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Trie (Trie(..))


import Agda.Utils.Except

import Agda.Utils.Empty (Empty)
import qualified Agda.Utils.Empty as Empty

import Agda.Utils.WithDefault

import Agda.Utils.Impossible

instance {-# OVERLAPPING #-} EmbPrj String where
  icod_   = icodeString
  value i = (! i) `fmap` gets stringE

instance EmbPrj Text where
  icod_   = icodeX textD textC
  value i = (! i) `fmap` gets textE

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
  icod_ () = icodeN' ()

  value = vcase valu where
    valu [] = valuN ()
    valu _  = malformed

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icod_ (a, b) = icodeN' (,) a b

  value = valueN (,)

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
  icod_ True  = icodeN' True
  icod_ False = icodeN 0 False

  value = vcase valu where
    valu []  = valuN True
    valu [0] = valuN False
    valu _   = malformed

instance EmbPrj FileType where
  icod_ AgdaFileType = icodeN' IsData
  icod_ MdFileType   = icodeN 0 IsRecord
  icod_ RstFileType  = icodeN 1 IsRecord
  icod_ TexFileType  = icodeN 2 IsRecord
  icod_ OrgFileType  = icodeN 3 IsRecord

  value = vcase $ \case
    []  -> valuN AgdaFileType
    [0] -> valuN MdFileType
    [1] -> valuN RstFileType
    [2] -> valuN TexFileType
    [3] -> valuN OrgFileType
    _   -> malformed

instance EmbPrj DataOrRecord where
  icod_ IsData   = icodeN' IsData
  icod_ IsRecord = icodeN 0 IsRecord

  value = vcase $ \case
    []  -> valuN IsData
    [0] -> valuN IsRecord
    _   -> malformed

instance EmbPrj AbsolutePath where
  icod_ file = do
    d <- asks absPathD
    liftIO $ flip fromMaybeM (H.lookup d file) $ do
      -- The path @file@ should be cached in the dictionary @d@.
      -- This seems not to be the case, thus, crash here.
      -- But leave some hints for the posterity why things could go so wrong.
      -- reportSLn "impossible" 10 -- does not work here
      putStrLn $ unlines $
        [ "Panic while serializing absolute path: " ++ show file
        , "The path could not be found in the dictionary:"
        ]
      putStrLn . show =<< H.toList d
      __IMPOSSIBLE__

  value m = do
    m :: TopLevelModuleName
            <- value m
    mf      <- gets modFile
    incs    <- gets includes
    (r, mf) <- liftIO $ findFile'' incs m mf
    modify $ \s -> s { modFile = mf }
    case r of
      Left err -> throwError $ findErrorToTypeError m err
      Right f  -> return f

instance EmbPrj a => EmbPrj (Position' a) where
  icod_ (P.Pn file pos line col) = icodeN' P.Pn file pos line col

  value = valueN P.Pn

instance Typeable b => EmbPrj (WithDefault b) where
  icod_ = \case
    Default -> icodeN' Default
    Value b -> icodeN' Value b

  value = vcase $ \case
    []  -> valuN Default
    [a] -> valuN Value a
    _ -> malformed

instance EmbPrj TopLevelModuleName where
  icod_ (TopLevelModuleName a b) = icodeN' TopLevelModuleName a b

  value = valueN TopLevelModuleName

instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
  icod_ xs = icodeNode =<< mapM icode xs
  value    = vcase (mapM value)
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = malformed

instance EmbPrj a => EmbPrj (NonemptyList a) where
  icod_ = icod_ . toList
  value = listCaseNe malformed return <=< value

instance (Ord a, Ord b, EmbPrj a, EmbPrj b) => EmbPrj (BiMap a b) where
  icod_ m = icode (BiMap.toList m)
  value m = BiMap.fromList <$> value m

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icod_ m = icode (Map.toList m)
  value m = Map.fromList `fmap` value m

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icod_ s = icode (Set.toList s)
  value s = Set.fromList `fmap` value s

instance EmbPrj IntSet where
  icod_ s = icode (IntSet.toList s)
  value s = IntSet.fromList <$> value s

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Trie a b) where
  icod_ (Trie a b)= icodeN' Trie a b

  value = valueN Trie

instance EmbPrj a => EmbPrj (Seq a) where
  icod_ s = icode (Fold.toList s)
  value s = Seq.fromList `fmap` value s

instance EmbPrj a => EmbPrj (P.Interval' a) where
  icod_ (P.Interval p q) = icodeN' P.Interval p q

  value = valueN P.Interval

-- | Ranges are always deserialised as 'noRange'.

instance EmbPrj Range where
  icod_ _ = icodeN' ()
  value _ = return noRange

-- | Ranges that should be serialised properly.

newtype SerialisedRange = SerialisedRange { underlyingRange :: Range }

instance EmbPrj SerialisedRange where
  icod_ (SerialisedRange r) =
    icodeN' (undefined :: SrcFile -> [IntervalWithoutFile] -> SerialisedRange)
            (P.rangeFile r) (P.rangeIntervals r)

  value = vcase valu where
    valu [a, b] = SerialisedRange <$> valuN P.intervalsToRange a b
    valu _      = malformed

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

instance EmbPrj Agda.Syntax.Fixity.Associativity where
  icod_ LeftAssoc  = icodeN' LeftAssoc
  icod_ RightAssoc = icodeN 1 RightAssoc
  icod_ NonAssoc   = icodeN 2 NonAssoc

  value = vcase valu where
    valu []  = valuN LeftAssoc
    valu [1] = valuN RightAssoc
    valu [2] = valuN NonAssoc
    valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.PrecedenceLevel where
  icod_ Unrelated   = icodeN' Unrelated
  icod_ (Related a) = icodeN' Related a

  value = vcase valu where
    valu []  = valuN Unrelated
    valu [a] = valuN Related a
    valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icod_ (Fixity a b c) = icodeN' Fixity a b c

  value = valueN Fixity

instance EmbPrj Agda.Syntax.Fixity.Fixity' where
  icod_ (Fixity' a b r) = icodeN' (\ a b -> Fixity' a b r) a b  -- discard theNameRange

  value = valueN (\ f n -> Fixity' f n noRange)

instance EmbPrj GenPart where
  icod_ (BindHole a b)   = icodeN 0 BindHole a b
  icod_ (NormalHole a b) = icodeN 1 NormalHole a b
  icod_ (WildHole a)     = icodeN 2 WildHole a
  icod_ (IdPart a)       = icodeN' IdPart a

  value = vcase valu where
    valu [0, a, b] = valuN BindHole a b
    valu [1, a, b] = valuN NormalHole a b
    valu [2, a]    = valuN WildHole a
    valu [a]       = valuN IdPart a
    valu _         = malformed

instance EmbPrj MetaId where
  icod_ (MetaId n) = icod_ n
  value i = MetaId <$> value i

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
  icod_ (A.Name a b c d e) = icodeMemo nameD nameC a $
    icodeN' (\ a b -> A.Name a b . underlyingRange) a b (SerialisedRange c) d e

  value = valueN (\a b c -> A.Name a b (underlyingRange c))

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
  icod_ (ArgInfo h r o fv) = icodeN' ArgInfo h r o fv

  value = valueN ArgInfo

instance EmbPrj NameId where
  icod_ (NameId a b) = icodeN' NameId a b

  value = valueN NameId

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icod_ m = icode (HMap.toList m)
  value m = HMap.fromList `fmap` value m

instance EmbPrj a => EmbPrj (WithHiding a) where
  icod_ (WithHiding a b) = icodeN' WithHiding a b

  value = valueN WithHiding

instance EmbPrj a => EmbPrj (Arg a) where
  icod_ (Arg i e) = icodeN' Arg i e

  value = valueN Arg

instance EmbPrj HasEta where
  icod_ YesEta = icodeN' YesEta
  icod_ NoEta  = icodeN 1 NoEta

  value = vcase valu where
    valu []  = valuN YesEta
    valu [1] = valuN NoEta
    valu _   = malformed

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

instance EmbPrj Origin where
  icod_ UserWritten = return 0
  icod_ Inserted    = return 1
  icod_ Reflected   = return 2
  icod_ CaseSplit   = return 3
  icod_ Substitution = return 4

  value 0 = return UserWritten
  value 1 = return Inserted
  value 2 = return Reflected
  value 3 = return CaseSplit
  value 4 = return Substitution
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
  icod_ (LitNat    a b)   = icodeN' LitNat a b
  icod_ (LitFloat  a b)   = icodeN 1 LitFloat a b
  icod_ (LitString a b)   = icodeN 2 LitString a b
  icod_ (LitChar   a b)   = icodeN 3 LitChar a b
  icod_ (LitQName  a b)   = icodeN 5 LitQName a b
  icod_ (LitMeta   a b c) = icodeN 6 LitMeta a b c
  icod_ (LitWord64 a b)   = icodeN 7 LitWord64 a b

  value = vcase valu where
    valu [a, b]       = valuN LitNat    a b
    valu [1, a, b]    = valuN LitFloat  a b
    valu [2, a, b]    = valuN LitString a b
    valu [3, a, b]    = valuN LitChar   a b
    valu [5, a, b]    = valuN LitQName  a b
    valu [6, a, b, c] = valuN LitMeta   a b c
    valu [7, a, b]    = valuN LitWord64 a b
    valu _            = malformed

instance EmbPrj IsAbstract where
  icod_ AbstractDef = icodeN 0 AbstractDef
  icod_ ConcreteDef = icodeN' ConcreteDef

  value = vcase valu where
    valu [0] = valuN AbstractDef
    valu []  = valuN ConcreteDef
    valu _   = malformed

instance EmbPrj Delayed where
  icod_ Delayed    = icodeN 0 Delayed
  icod_ NotDelayed = icodeN' NotDelayed

  value = vcase valu where
    valu [0] = valuN Delayed
    valu []  = valuN NotDelayed
    valu _   = malformed

instance EmbPrj Impossible where
  icod_ (Impossible a b)  = icodeN 0 Impossible a b
  icod_ (Unreachable a b) = icodeN 1 Unreachable a b
  icod_ (ImpMissingDefinitions a b) = icodeN 2 ImpMissingDefinitions a b

  value = vcase valu where
    valu [0, a, b] = valuN Impossible  a b
    valu [1, a, b] = valuN Unreachable a b
    valu [2, a, b] = valuN ImpMissingDefinitions a b
    valu _         = malformed

instance EmbPrj Empty where
  icod_ a = icod_ =<< lift (Empty.toImpossible a)

  value = fmap throwImpossible . value
