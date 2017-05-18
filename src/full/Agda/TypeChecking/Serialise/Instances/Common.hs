{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverlappingInstances       #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Common (SerialisedRange(..)) where

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State.Strict (gets, modify)
import Control.Exception

import Data.Array.IArray
import Data.Word
import qualified Data.ByteString.Lazy as L
import qualified Data.Foldable as Fold
import Data.Hashable
import qualified Data.HashTable.IO as H
import Data.Int (Int32)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Traversable ( mapM )

#if __GLASGOW_HASKELL__ <= 708
import Data.Typeable ( Typeable )
#endif

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
import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.FileName
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Trie

import Agda.Utils.Except

import Agda.Utils.Empty (Empty)
import qualified Agda.Utils.Empty as Empty

#include "undefined.h"
import Agda.Utils.Impossible

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} EmbPrj String where
#else
instance EmbPrj String where
#endif
  icod_   = icodeString
  value i = (! i) `fmap` gets stringE

instance EmbPrj L.ByteString where
  icod_   = icodeX bstringD bstringC
  value i = (! i) `fmap` gets bstringE

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

instance EmbPrj AbsolutePath where
  icod_ file = do
    d <-  asks absPathD
    liftIO $ fromMaybe __IMPOSSIBLE__ <$> H.lookup d file

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

instance EmbPrj TopLevelModuleName where
  icod_ (TopLevelModuleName a b) = icodeN' TopLevelModuleName a b

  value = valueN TopLevelModuleName

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
#else
instance EmbPrj a => EmbPrj [a] where
#endif
  icod_ xs = icodeNode =<< mapM icode xs
  value    = vcase (mapM value)
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = malformed

instance (Ord a, Ord b, EmbPrj a, EmbPrj b) => EmbPrj (BiMap a b) where
  icod_ m = icode (BiMap.toList m)
  value m = BiMap.fromList <$> value m

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icod_ m = icode (Map.toList m)
  value m = Map.fromList `fmap` value m

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icod_ s = icode (Set.toList s)
  value s = Set.fromList `fmap` value s

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
#if __GLASGOW_HASKELL__ <= 708
  deriving (Typeable)
#endif

instance EmbPrj SerialisedRange where
  icod_ (SerialisedRange r) =
    icodeN' (undefined :: SrcFile -> [IntervalWithoutFile] -> SerialisedRange)
            (P.rangeFile r) (P.rangeIntervals r)

  value = vcase valu where
    valu [a, b] = SerialisedRange <$> valuN P.intervalsToRange a b
    valu _      = malformed

instance EmbPrj C.Name where
  icod_ (C.NoName a b) = icodeN 0 C.NoName a b
  icod_ (C.Name r xs)  = icodeN' C.Name r xs

  value = vcase valu where
    valu [0, a, b] = valuN C.NoName a b
    valu [r, xs]   = valuN C.Name   r xs
    valu _         = malformed

instance EmbPrj NamePart where
  icod_ Hole   = icodeN' Hole
  icod_ (Id a) = icodeN' Id a

  value = vcase valu where
    valu []  = valuN Hole
    valu [a] = valuN Id a
    valu _   = malformed

instance EmbPrj C.QName where
  icod_ (Qual    a b) = icodeN' Qual a b
  icod_ (C.QName a  ) = icodeN' C.QName a

  value = vcase valu where
    valu [a, b] = valuN Qual    a b
    valu [a]    = valuN C.QName a
    valu _      = malformed

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
  icod_ (BindHole a)   = icodeN 0 BindHole a
  icod_ (NormalHole a) = icodeN 1 NormalHole a
  icod_ (WildHole a)   = icodeN 2 WildHole a
  icod_ (IdPart a)     = icodeN' IdPart a

  value = vcase valu where
    valu [0, a] = valuN BindHole a
    valu [1, a] = valuN NormalHole a
    valu [2, a] = valuN WildHole a
    valu [a]    = valuN IdPart a
    valu _      = malformed

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
  icod_ (A.Name a b c d) = icodeMemo nameD nameC a $
    icodeN' (\ a b -> A.Name a b . underlyingRange) a b (SerialisedRange c) d

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
  icod_ (ArgInfo h r o v) = icodeN' ArgInfo h r o v

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

instance EmbPrj a => EmbPrj (Dom a) where
  icod_ (Dom i e) = icodeN' Dom i e

  value = valueN Dom

instance EmbPrj Induction where
  icod_ Inductive   = icodeN' Inductive
  icod_ CoInductive = icodeN 1 CoInductive

  value = vcase valu where
    valu []  = valuN Inductive
    valu [1] = valuN CoInductive
    valu _   = malformed

instance EmbPrj Hiding where
  icod_ Hidden    = return 0
  icod_ NotHidden = return 1
  icod_ Instance  = return 2

  value 0 = return Hidden
  value 1 = return NotHidden
  value 2 = return Instance
  value _ = malformed

instance EmbPrj Relevance where
  icod_ Relevant       = return 0
  icod_ Irrelevant     = return 1
  icod_ (Forced Small) = return 2
  icod_ (Forced Big)   = return 3
  icod_ NonStrict      = return 4

  value 0 = return Relevant
  value 1 = return Irrelevant
  value 2 = return (Forced Small)
  value 3 = return (Forced Big)
  value 4 = return NonStrict
  value _ = malformed

instance EmbPrj Origin where
  icod_ UserWritten = return 0
  icod_ Inserted    = return 1
  icod_ Reflected   = return 2

  value 0 = return UserWritten
  value 1 = return Inserted
  value 2 = return Reflected
  value _ = malformed

instance EmbPrj ConOrigin where
  icod_ ConOSystem = return 0
  icod_ ConOCon    = return 1
  icod_ ConORec    = return 2

  value 0 = return ConOSystem
  value 1 = return ConOCon
  value 2 = return ConORec
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

  value = vcase valu where
    valu [a, b]       = valuN LitNat    a b
    valu [1, a, b]    = valuN LitFloat  a b
    valu [2, a, b]    = valuN LitString a b
    valu [3, a, b]    = valuN LitChar   a b
    valu [5, a, b]    = valuN LitQName  a b
    valu [6, a, b, c] = valuN LitMeta   a b c
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

  value = vcase valu where
    valu [0, a, b] = valuN Impossible  a b
    valu [1, a, b] = valuN Unreachable a b
    valu _         = malformed

instance EmbPrj Empty where
  icod_ a = icod_ =<< lift (Empty.toImpossible a)

  value = fmap throwImpossible . value
