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
  icod_ i = icode2' (int32 q) (int32 r)
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
  icod_ () = icode0'

  value = vcase valu where
    valu [] = valu0 ()
    valu _  = malformed

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icod_ (a, b) = icode2' a b

  value = value2 (,)

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icod_ (a, b, c) = icode3' a b c

  value = value3 (,,)

instance (EmbPrj a, EmbPrj b) => EmbPrj (Either a b) where
  icod_ (Left  x) = icode1 0 x
  icod_ (Right x) = icode1 1 x

  value = vcase valu where
    valu [0, x] = valu1 Left  x
    valu [1, x] = valu1 Right x
    valu _   = malformed

instance EmbPrj a => EmbPrj (Maybe a) where
  icod_ Nothing  = icode0'
  icod_ (Just x) = icode1' x

  value = vcase valu where
    valu []  = valu0 Nothing
    valu [x] = valu1 Just x
    valu _   = malformed

instance EmbPrj a => EmbPrj (Strict.Maybe a) where
  icod_ m = icode (Strict.toLazy m)
  value m = Strict.toStrict `fmap` value m

instance EmbPrj Bool where
  icod_ True  = icode0'
  icod_ False = icode0 0

  value = vcase valu where
    valu []  = valu0 True
    valu [0] = valu0 False
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
  icod_ (P.Pn file pos line col) = icode4' file pos line col

  value = value4 P.Pn

instance EmbPrj TopLevelModuleName where
  icod_ (TopLevelModuleName a b) = icode2' a b

  value = value2 TopLevelModuleName

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
#else
instance EmbPrj a => EmbPrj [a] where
#endif
  icod_ xs = icodeN =<< mapM icode xs
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
  icod_ (Trie a b)= icode2' a b

  value = value2 Trie

instance EmbPrj a => EmbPrj (Seq a) where
  icod_ s = icode (Fold.toList s)
  value s = Seq.fromList `fmap` value s

instance EmbPrj a => EmbPrj (P.Interval' a) where
  icod_ (P.Interval p q) = icode2' p q

  value = value2 P.Interval

-- | Ranges are always deserialised as 'noRange'.

instance EmbPrj Range where
  icod_ _ = icode0'
  value _ = return noRange

-- | Ranges that should be serialised properly.

newtype SerialisedRange = SerialisedRange { underlyingRange :: Range }
#if __GLASGOW_HASKELL__ <= 708
  deriving (Typeable)
#endif

instance EmbPrj SerialisedRange where
  icod_ (SerialisedRange r) =
    icode2' (P.rangeFile r) (P.rangeIntervals r)

  value = vcase valu where
    valu [a, b] = SerialisedRange <$> valu2 P.intervalsToRange a b
    valu _      = malformed

instance EmbPrj C.Name where
  icod_ (C.NoName a b) = icode2 0 a b
  icod_ (C.Name r xs)  = icode2' r xs

  value = vcase valu where
    valu [0, a, b] = valu2 C.NoName a b
    valu [r, xs]   = valu2 C.Name   r xs
    valu _         = malformed

instance EmbPrj NamePart where
  icod_ Hole   = icode0'
  icod_ (Id a) = icode1' a

  value = vcase valu where
    valu []  = valu0 Hole
    valu [a] = valu1 Id a
    valu _   = malformed

instance EmbPrj C.QName where
  icod_ (Qual    a b) = icode2' a b
  icod_ (C.QName a  ) = icode1' a

  value = vcase valu where
    valu [a, b] = valu2 Qual    a b
    valu [a]    = valu1 C.QName a
    valu _      = malformed

instance EmbPrj Agda.Syntax.Fixity.Associativity where
  icod_ LeftAssoc  = icode0'
  icod_ RightAssoc = icode0 1
  icod_ NonAssoc   = icode0 2

  value = vcase valu where
    valu []  = valu0 LeftAssoc
    valu [1] = valu0 RightAssoc
    valu [2] = valu0 NonAssoc
    valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.PrecedenceLevel where
  icod_ Unrelated   = icode0'
  icod_ (Related a) = icode1' a

  value = vcase valu where
    valu []  = valu0 Unrelated
    valu [a] = valu1 Related a
    valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icod_ (Fixity a b c) = icode3' a b c

  value = value3 Fixity

instance EmbPrj Agda.Syntax.Fixity.Fixity' where
  icod_ (Fixity' a b _) = icode2' a b  -- discard theNameRange

  value = value2 (\ f n -> Fixity' f n noRange)

instance EmbPrj GenPart where
  icod_ (BindHole a)   = icode1 0 a
  icod_ (NormalHole a) = icode1 1 a
  icod_ (WildHole a)   = icode1 2 a
  icod_ (IdPart a)     = icode1' a

  value = vcase valu where
    valu [0, a] = valu1 BindHole a
    valu [1, a] = valu1 NormalHole a
    valu [2, a] = valu1 WildHole a
    valu [a]    = valu1 IdPart a
    valu _      = malformed

instance EmbPrj MetaId where
  icod_ (MetaId n) = icod_ n
  value i = MetaId <$> value i

instance EmbPrj A.QName where
  icod_ n@(A.QName a b) = icodeMemo qnameD qnameC (qnameId n) $ icode2' a b

  value = value2 A.QName

instance EmbPrj A.AmbiguousQName where
  icod_ (A.AmbQ a) = icode a
  value n          = A.AmbQ `fmap` value n

instance EmbPrj A.ModuleName where
  icod_ (A.MName a) = icode a
  value n           = A.MName `fmap` value n

instance EmbPrj A.Name where
  icod_ (A.Name a b c d) = icodeMemo nameD nameC a $
    icode4' a b (SerialisedRange c) d

  value = value4 (\a b c -> A.Name a b (underlyingRange c))

instance EmbPrj a => EmbPrj (C.FieldAssignment' a) where
  icod_ (C.FieldAssignment a b) = icode2' a b

  value = value2 C.FieldAssignment

instance (EmbPrj s, EmbPrj t) => EmbPrj (Named s t) where
  icod_ (Named a b) = icode2' a b

  value = value2 Named

instance EmbPrj a => EmbPrj (Ranged a) where
  icod_ (Ranged r x) = icode2' r x

  value = value2 Ranged

instance EmbPrj ArgInfo where
  icod_ (ArgInfo h r o v) = icode4' h r o v

  value = value4 ArgInfo

instance EmbPrj NameId where
  icod_ (NameId a b) = icode2' a b

  value = value2 NameId

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icod_ m = icode (HMap.toList m)
  value m = HMap.fromList `fmap` value m

instance EmbPrj a => EmbPrj (WithHiding a) where
  icod_ (WithHiding a b) = icode2' a b

  value = value2 WithHiding

instance EmbPrj a => EmbPrj (Arg a) where
  icod_ (Arg i e) = icode2' i e

  value = value2 Arg

instance EmbPrj a => EmbPrj (Dom a) where
  icod_ (Dom i e) = icode2' i e

  value = value2 Dom

instance EmbPrj Induction where
  icod_ Inductive   = icode0'
  icod_ CoInductive = icode0 1

  value = vcase valu where
    valu []  = valu0 Inductive
    valu [1] = valu0 CoInductive
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
  icod_ (LitNat    a b)   = icode2' a b
  icod_ (LitFloat  a b)   = icode2 1 a b
  icod_ (LitString a b)   = icode2 2 a b
  icod_ (LitChar   a b)   = icode2 3 a b
  icod_ (LitQName  a b)   = icode2 5 a b
  icod_ (LitMeta   a b c) = icode3 6 a b c

  value = vcase valu where
    valu [a, b]       = valu2 LitNat    a b
    valu [1, a, b]    = valu2 LitFloat  a b
    valu [2, a, b]    = valu2 LitString a b
    valu [3, a, b]    = valu2 LitChar   a b
    valu [5, a, b]    = valu2 LitQName  a b
    valu [6, a, b, c] = valu3 LitMeta   a b c
    valu _            = malformed

instance EmbPrj IsAbstract where
  icod_ AbstractDef = icode0 0
  icod_ ConcreteDef = icode0'

  value = vcase valu where
    valu [0] = valu0 AbstractDef
    valu []  = valu0 ConcreteDef
    valu _   = malformed

instance EmbPrj Delayed where
  icod_ Delayed    = icode0 0
  icod_ NotDelayed = icode0'

  value = vcase valu where
    valu [0] = valu0 Delayed
    valu []  = valu0 NotDelayed
    valu _   = malformed


instance EmbPrj Impossible where
  icod_ (Impossible a b)  = icode2 0 a b
  icod_ (Unreachable a b) = icode2 1 a b

  value = vcase valu where
    valu [0, a, b] = valu2 Impossible  a b
    valu [1, a, b] = valu2 Unreachable a b
    valu _         = malformed

instance EmbPrj Empty where
  icod_ a = icode1' =<< lift (Empty.toImpossible a)

  value = vcase valu where
    valu [a] = valu1 throwImpossible a
    valu _ = malformed
