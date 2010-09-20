{-# LANGUAGE OverlappingInstances,
             TypeSynonymInstances,
             IncoherentInstances,
             ExistentialQuantification,
             ScopedTypeVariables,
             CPP
             #-}
{-# OPTIONS_GHC -O2 #-}

-- | Structure-sharing serialisation of Agda interface files.

-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-
-- NOTE: Every time the interface format is changed the interface
-- version number should be bumped _in the same patch_.
-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-

module Agda.TypeChecking.Serialise
  ( encode
  , encodeFile
  , decode
  , decodeFile
  , EmbPrj
  )
  where

import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Error
import Data.Array.IArray
import Data.Bits (shiftR)
import Data.Word
import Data.ByteString.Lazy as L
import Data.HashTable (HashTable)
import qualified Data.HashTable as H
import Data.Int (Int32, Int64)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.List as List
import Data.Function
import Data.Typeable
import qualified Codec.Compression.GZip as G

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position (Position(..), Range)
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal
import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP
import Agda.Interaction.FindFile

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20100920 * 10 + 0

type Node = [Int32] -- constructor tag (maybe omitted) and arg indices

data Dict = Dict{ nodeD     :: !(HashTable Node    Int32)
                , stringD   :: !(HashTable String  Int32)
                , integerD  :: !(HashTable Integer Int32)
                , doubleD   :: !(HashTable Double  Int32)
                , nodeC     :: !(IORef Int32)  -- counters for fresh indexes
                , stringC   :: !(IORef Int32)
                , integerC  :: !(IORef Int32)
                , doubleC   :: !(IORef Int32)
                , fileMod   :: !SourceToModule
                }

data U    = forall a . Typeable a => U !a
type Memo = HashTable (Int32, Int32) U    -- (node index, type rep key)

data St = St
  { nodeE     :: !(Array Int32 Node)
  , stringE   :: !(Array Int32 String)
  , integerE  :: !(Array Int32 Integer)
  , doubleE   :: !(Array Int32 Double)
  , nodeMemo  :: !Memo
  , modFile   :: !ModuleToSource
    -- ^ Maps module names to file names. This is the only component
    -- of the state which is updated by the decoder.
  , includes  :: [AbsolutePath]
    -- ^ The include directories.
  }

-- | Monad used by the encoder.

type S a = ReaderT Dict IO a

-- | Monad used by the decoder.
--
-- 'TCM' is not used because the associated overheads would make
-- decoding slower.

type R a = ErrorT TypeError (StateT St IO) a

-- | Throws an error which is suitable when the data stream is
-- malformed.

malformed :: R a
malformed = throwError $ GenericError "Malformed input."

class Typeable a => EmbPrj a where
  icode :: a -> S Int32
  value :: Int32 -> R a

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encode :: EmbPrj a => a -> TCM ByteString
encode a = do
    fileMod <- sourceToModule
    liftIO $ do
      newD@(Dict nD sD iD dD _ _ _ _ _) <- emptyDict fileMod
      root <- runReaderT (icode a) newD
      nL <- l nD; sL <- l sD; iL <- l iD; dL <- l dD
      return $ B.encode currentInterfaceVersion `L.append`
               G.compress (B.encode (root, nL, sL, iL, dL))
  where l = fmap (List.map fst . List.sortBy (compare `on` snd)) . H.toList

-- | Decodes something. The result depends on the include path.
--
-- Returns 'Nothing' if the input does not start with the right magic
-- number or some other decoding error is encountered.

decode :: EmbPrj a => ByteString -> TCM (Maybe a)
decode s = do
  mf   <- stModuleToSource <$> get
  incs <- getIncludeDirs

  -- Note that B.runGetState and G.decompress can raise errors if the
  -- input is malformed. The decoder is (intended to be) strict enough
  -- to ensure that all such errors can be caught by the handler here.

  (mf, x) <- liftIO $ E.handle (\(E.ErrorCall {}) -> noResult) $ do

    (ver, s, _) <- return $ B.runGetState B.get s 0
    if ver /= currentInterfaceVersion
     then noResult
     else do

      ((r, nL, sL, iL, dL), s, _) <-
        return $ B.runGetState B.get (G.decompress s) 0
      if s /= L.empty
         -- G.decompress seems to throw away garbage at the end, so
         -- the then branch is possibly dead code.
       then noResult
       else do

        st <- St (ar nL) (ar sL) (ar iL) (ar dL)
                <$> liftIO (H.new (==) hashInt2)
                <*> return mf <*> return incs
        (r, st) <- runStateT (runErrorT (value r)) st
        return (Just (modFile st), case r of
          Left  _ -> Nothing
          Right x -> Just x)

  case mf of
    Nothing -> return ()
    Just mf -> modify $ \s -> s { stModuleToSource = mf }

  return x

  where
  ar l = listArray (0, List.genericLength l - 1) l

  noResult = return (Nothing, Nothing)

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encodeFile :: EmbPrj a
           => FilePath
              -- ^ The encoded data is written to this file.
           -> a
              -- ^ Something.
           -> TCM ()
encodeFile f x = liftIO . L.writeFile f =<< encode x

-- | Decodes something. The result depends on the include path.
--
-- Returns 'Nothing' if the file does not start with the right magic
-- number or some other decoding error is encountered.

decodeFile :: EmbPrj a => FilePath -> TCM (Maybe a)
decodeFile f = decode =<< liftIO (L.readFile f)


instance EmbPrj String where
  icode   = icodeX stringD stringC
  value i = (! i) `fmap` gets stringE

instance EmbPrj Integer where
  icode   = icodeX integerD integerC
  value i = (! i) `fmap` gets integerE

instance EmbPrj Int32 where
  icode i = return i
  value i = return i

instance EmbPrj Int where
  icode i = return (fromIntegral i)
  value i = return (fromIntegral i)

instance EmbPrj Char where
  icode c = return (fromIntegral $ fromEnum c)
  value i = return (toEnum $ fromInteger $ toInteger i)

instance EmbPrj Double where
  icode   = icodeX doubleD doubleC
  value i = (! i) `fmap` gets doubleE

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icode (a, b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 (,) a b
                           valu _      = malformed

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icode (a, b, c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 (,,) a b c
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Maybe a) where
  icode Nothing  = icode0'
  icode (Just x) = icode1' x
  value = vcase valu where valu []  = valu0 Nothing
                           valu [x] = valu1 Just x
                           valu _   = malformed

instance EmbPrj Bool where
  icode True  = icode0 0
  icode False = icode0 1
  value = vcase valu where valu [0] = valu0 True
                           valu [1] = valu0 False
                           valu _   = malformed

instance EmbPrj AbsolutePath where
  icode file = do
    mm <- M.lookup file . fileMod <$> ask
    case mm of
      Just m  -> icode m
      Nothing -> __IMPOSSIBLE__
  value m = do
    m       <- value m
    mf      <- modFile  <$> get
    incs    <- includes <$> get
    (r, mf) <- liftIO $ findFile'' incs m mf
    modify $ \s -> s { modFile = mf }
    case r of
      Left err -> throwError $ findErrorToTypeError m err
      Right f  -> return f

instance EmbPrj Position where
  icode (P.Pn file pos line col) = icode4' file pos line col
  value = vcase valu
    where
    valu [f, p, l, c] = valu4 P.Pn f p l c
    valu _            = malformed

instance EmbPrj TopLevelModuleName where
  icode (TopLevelModuleName a) = icode1' a
  value = vcase valu where valu [a] = valu1 TopLevelModuleName a
                           valu _   = malformed

instance EmbPrj a => EmbPrj [a] where
  icode xs = icodeN =<< mapM icode xs
  value = vcase $ mapM value
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = malformed

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icode m = icode (M.toList m)
  value m = M.fromList `fmap` value m

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icode s = icode (S.toList s)
  value s = S.fromList `fmap` value s

instance EmbPrj P.Interval where
  icode (P.Interval p q) = icode2' p q
  value = vcase valu where valu [p, q] = valu2 P.Interval p q
                           valu _      = malformed

instance EmbPrj Range where
  icode (P.Range is) = icode1' is
  value = vcase valu where valu [is] = valu1 P.Range is
                           valu _    = malformed

instance EmbPrj HR.Range where
  icode (HR.Range a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 HR.Range a b
                           valu _      = malformed

instance EmbPrj C.Name where
  icode (C.NoName a b) = icode2 0 a b
  icode (C.Name r xs)  = icode2 1 r xs
  value = vcase valu where valu [0, a, b]  = valu2 C.NoName a b
                           valu [1, r, xs] = valu2 C.Name   r xs
                           valu _          = malformed

instance EmbPrj NamePart where
  icode Hole   = icode0'
  icode (Id a) = icode1' a
  value = vcase valu where valu []  = valu0 Hole
                           valu [a] = valu1 Id a
                           valu _   = malformed

instance EmbPrj C.QName where
  icode (Qual    a b) = icode2' a b
  icode (C.QName a  ) = icode1' a
  value = vcase valu where valu [a, b] = valu2 Qual    a b
                           valu [a]    = valu1 C.QName a
                           valu _      = malformed

instance EmbPrj Scope where
  icode (Scope a b c d e f) = icode6' a b c d e f
  value = vcase valu where valu [a, b, c, d, e, f] = valu6 Scope a b c d e f
                           valu _                  = malformed

instance EmbPrj Access where
  icode PrivateAccess = icode0 0
  icode PublicAccess  = icode0 1
  value = vcase valu where valu [0] = valu0 PrivateAccess
                           valu [1] = valu0 PublicAccess
                           valu _   = malformed

instance EmbPrj NameSpace where
  icode (NameSpace a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameSpace a b
                           valu _      = malformed

instance EmbPrj AbstractName where
  icode (AbsName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 AbsName a b
                           valu _      = malformed

instance EmbPrj AbstractModule where
  icode (AbsModule a) = icode a
  value n = AbsModule `fmap` value n

instance EmbPrj KindOfName where
  icode DefName = icode0 0
  icode ConName = icode0 1
  value = vcase valu where valu [0] = valu0 DefName
                           valu [1] = valu0 ConName
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icode (LeftAssoc  a b) = icode2 0 a b
  icode (RightAssoc a b) = icode2 1 a b
  icode (NonAssoc   a b) = icode2 2 a b
  value = vcase valu where valu [0, a, b] = valu2 LeftAssoc  a b
                           valu [1, a, b] = valu2 RightAssoc a b
                           valu [2, a, b] = valu2 NonAssoc   a b
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity' where
  icode (Fixity' a b) = icode2' a b
  value = vcase valu where valu [a,b] = valu2 Fixity' a b
                           valu _ = malformed

instance EmbPrj GenPart where
    icode (BindHole a)   = icode1 0 a
    icode (NormalHole a) = icode1 1 a
    icode (IdPart a)     = icode1 2 a
    value = vcase valu where valu [0, a] = valu1 BindHole a
                             valu [1, a] = valu1 NormalHole a
                             valu [2, a] = valu1 IdPart a
                             valu _      = malformed

instance EmbPrj A.QName where
  icode (A.QName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 A.QName a b
                           valu _      = malformed

instance EmbPrj A.ModuleName where
  icode (A.MName a) = icode a
  value n = A.MName `fmap` value n

instance EmbPrj A.Name where
  icode (A.Name a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 A.Name a b c d
                           valu _            = malformed

instance EmbPrj NameId where
  icode (NameId a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameId a b
                           valu _      = malformed

instance EmbPrj Signature where
  icode (Sig a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Sig a b
                           valu _      = malformed

instance EmbPrj Section where
  icode (Section a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Section a b
                           valu _      = malformed

instance EmbPrj Telescope where
  icode EmptyTel        = icode0'
  icode (ExtendTel a b) = icode2' a b
  value = vcase valu where valu []     = valu0 EmptyTel
                           valu [a, b] = valu2 ExtendTel a b
                           valu _      = malformed

instance EmbPrj Permutation where
  icode (Perm a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Perm a b
                           valu _      = malformed

instance (EmbPrj a) => EmbPrj (Agda.Syntax.Common.Arg a) where
  icode (Arg a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Arg a b c
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Common.Induction where
  icode Inductive   = icode0 0
  icode CoInductive = icode0 1
  value = vcase valu where valu [0] = valu0 Inductive
                           valu [1] = valu0 CoInductive
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Common.Hiding where
  icode Hidden    = icode0 0
  icode NotHidden = icode0 1
  value = vcase valu where valu [0] = valu0 Hidden
                           valu [1] = valu0 NotHidden
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Common.Relevance where
  icode Relevant   = icode0 0
  icode Irrelevant = icode0 1
  icode Forced     = icode0 2
  value = vcase valu where valu [0] = valu0 Relevant
                           valu [1] = valu0 Irrelevant
                           valu [2] = valu0 Forced
                           valu _   = malformed

instance EmbPrj I.Type where
  icode (El a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 El a b
                           valu _      = malformed

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icode (Abs a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Abs a b
                           valu _      = malformed

instance EmbPrj I.Term where
  icode (Var      a b) = icode2 0 a b
  icode (Lam      a b) = icode2 1 a b
  icode (Lit      a  ) = icode1 2 a
  icode (Def      a b) = icode2 3 a b
  icode (Con      a b) = icode2 4 a b
  icode (Pi       a b) = icode2 5 a b
  icode (Fun      a b) = icode2 6 a b
  icode (Sort     a  ) = icode1 7 a
  icode (MetaV    a b) = __IMPOSSIBLE__
  value = vcase valu where valu [0, a, b] = valu2 Var   a b
                           valu [1, a, b] = valu2 Lam   a b
                           valu [2, a]    = valu1 Lit   a
                           valu [3, a, b] = valu2 Def   a b
                           valu [4, a, b] = valu2 Con   a b
                           valu [5, a, b] = valu2 Pi    a b
                           valu [6, a, b] = valu2 Fun   a b
                           valu [7, a]    = valu1 Sort  a
                           valu _         = malformed

instance EmbPrj I.Sort where
  icode (Type  a  ) = icode1 0 a
  icode Prop        = icode0 1
  icode (Lub   a b) = icode2 2 a b
  icode (Suc   a  ) = icode1 3 a
  icode (MetaS a b) = __IMPOSSIBLE__
  icode Inf         = icode0 4
  icode (DLub a b)  = icode2 5 a b
  value = vcase valu where valu [0, a]    = valu1 Type  a
                           valu [1]       = valu0 Prop
                           valu [2, a, b] = valu2 Lub   a b
                           valu [3, a]    = valu1 Suc   a
                           valu [4]       = valu0 Inf
                           valu [5, a, b] = valu2 DLub a b
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Literal.Literal where
  icode (LitInt    a b) = icode2 0 a b
  icode (LitFloat  a b) = icode2 1 a b
  icode (LitString a b) = icode2 2 a b
  icode (LitChar   a b) = icode2 3 a b
  icode (LitLevel  a b) = icode2 4 a b
  icode (LitQName  a b) = icode2 5 a b
  value = vcase valu where valu [0, a, b] = valu2 LitInt    a b
                           valu [1, a, b] = valu2 LitFloat  a b
                           valu [2, a, b] = valu2 LitString a b
                           valu [3, a, b] = valu2 LitChar   a b
                           valu [4, a, b] = valu2 LitLevel  a b
                           valu [5, a, b] = valu2 LitQName  a b
                           valu _         = malformed

instance EmbPrj DisplayForm where
  icode (Display a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Display a b c
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Open a) where
  icode (OpenThing a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 OpenThing a b
                           valu _      = malformed

instance EmbPrj CtxId where
  icode (CtxId a) = icode a
  value n = CtxId `fmap` value n

instance EmbPrj DisplayTerm where
  icode (DTerm    a  ) = icode1' a
  icode (DWithApp a b) = icode2' a b
  value = vcase valu where valu [a]    = valu1 DTerm a
                           valu [a, b] = valu2 DWithApp a b
                           valu _      = malformed

instance EmbPrj MutualId where
  icode (MutId a) = icode a
  value n = MutId `fmap` value n

instance EmbPrj Definition where
  icode (Defn a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Defn a b c d e
                           valu _               = malformed

instance EmbPrj HaskellRepresentation where
  icode (HsType a)   = icode1 0 a
  icode (HsDefn a b) = icode2 1 a b

  value = vcase valu where
    valu [0, a]    = valu1 HsType a
    valu [1, a, b] = valu2 HsDefn a b
    valu _         = malformed

instance EmbPrj Polarity where
  icode Covariant     = icode0 0
  icode Contravariant = icode0 1
  icode Invariant     = icode0 2

  value = vcase valu where
    valu [0] = valu0 Covariant
    valu [1] = valu0 Contravariant
    valu [2] = valu0 Invariant
    valu _   = malformed

instance EmbPrj Occurrence where
  icode Positive = icode0 0
  icode Negative = icode0 1
  icode Unused   = icode0 2

  value = vcase valu where
    valu [0] = valu0 Positive
    valu [1] = valu0 Negative
    valu [2] = valu0 Unused
    valu _   = malformed

instance EmbPrj Defn where
  icode (Axiom       a)                     = icode1 0 a
  icode (Function    a b c d e f g)         = icode7 1 a b c d e f g
  icode (Datatype    a b c d e f g h i j)   = icode10 2 a b c d e f g h i j
  icode (Record      a b c d e f g h i j k) = icode11 3 a b c d e f g h i j k
  icode (Constructor a b c d e f)           = icode6 4 a b c d e f
  icode (Primitive   a b c)                 = icode3 5 a b c
  value = vcase valu where
    valu [0, a]                               = valu1 Axiom       a
    valu [1, a, b, c, d, e, f, g]             = valu7 Function    a b c d e f g
    valu [2, a, b, c, d, e, f, g, h, i, j]    = valu10 Datatype   a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h, i, j, k] = valu11 Record     a b c d e f g h i j k
    valu [4, a, b, c, d, e, f]                = valu6 Constructor a b c d e f
    valu [5, a, b, c]                         = valu3 Primitive   a b c
    valu _                                    = malformed

instance EmbPrj a => EmbPrj (Case a) where
  icode (Branches a b c) = icode3' a b c

  value = vcase valu where
    valu [a, b, c] = valu3 Branches a b c
    valu _         = malformed

instance EmbPrj CompiledClauses where
  icode Fail       = icode0 0
  icode (Done a b) = icode2 1 a b
  icode (Case a b) = icode2 2 a b

  value = vcase valu where
    valu [0]       = valu0 Fail
    valu [1, a, b] = valu2 Done a b
    valu [2, a, b] = valu2 Case a b
    valu _         = malformed

instance EmbPrj FunctionInverse where
  icode NotInjective = icode0'
  icode (Inverse a)  = icode1' a
  value = vcase valu where valu []  = valu0 NotInjective
                           valu [a] = valu1 Inverse a
                           valu _   = malformed

instance EmbPrj TermHead where
  icode SortHead    = icode0 0
  icode PiHead      = icode0 1
  icode (ConHead a) = icode1 2 a
  value = vcase valu where valu [0]    = return SortHead
                           valu [1]    = return PiHead
                           valu [2, a] = valu1 ConHead a
                           valu _      = malformed

instance EmbPrj Agda.Syntax.Common.IsAbstract where
  icode AbstractDef = icode0 0
  icode ConcreteDef = icode0 1
  value = vcase valu where valu [0] = valu0 AbstractDef
                           valu [1] = valu0 ConcreteDef
                           valu _   = malformed

instance EmbPrj I.Clauses where
  icode (Clauses a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Clauses a b
                           valu _      = malformed

instance EmbPrj I.Clause where
  icode (Clause a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Clause a b c d e
                           valu _               = malformed

instance EmbPrj I.ClauseBody where
  icode (Body   a) = icode1 0 a
  icode (Bind   a) = icode1 1 a
  icode (NoBind a) = icode1 2 a
  icode NoBody     = icode0'
  value = vcase valu where valu [0, a] = valu1 Body   a
                           valu [1, a] = valu1 Bind   a
                           valu [2, a] = valu1 NoBind a
                           valu []     = valu0 NoBody
                           valu _      = malformed

instance EmbPrj Delayed where
  icode Delayed    = icode0 0
  icode NotDelayed = icode0 1
  value = vcase valu where valu [0] = valu0 Delayed
                           valu [1] = valu0 NotDelayed
                           valu _   = malformed

instance EmbPrj I.Pattern where
  icode (VarP a    ) = icode1 0 a
  icode (ConP a b c) = icode3 1 a b c
  icode (LitP a    ) = icode1 2 a
  icode (DotP a    ) = icode1 3 a
  value = vcase valu where valu [0, a]       = valu1 VarP a
                           valu [1, a, b, c] = valu3 ConP a b c
                           valu [2, a]       = valu1 LitP a
                           valu [3, a]       = valu1 DotP a
                           valu _            = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icode (Prim    a) = icode1 0 a
  icode (Builtin a) = icode1 1 a
  value = vcase valu where valu [0, a] = valu1 Prim    a
                           valu [1, a] = valu1 Builtin a
                           valu _      = malformed

instance EmbPrj HP.NameKind where
  icode HP.Bound           = icode0 0
  icode (HP.Constructor a) = icode1 1 a
  icode HP.Datatype        = icode0 2
  icode HP.Field           = icode0 3
  icode HP.Function        = icode0 4
  icode HP.Module          = icode0 5
  icode HP.Postulate       = icode0 6
  icode HP.Primitive       = icode0 7
  icode HP.Record          = icode0 8

  value = vcase valu where
    valu [0]     = valu0 HP.Bound
    valu [1 , a] = valu1 HP.Constructor a
    valu [2]     = valu0 HP.Datatype
    valu [3]     = valu0 HP.Field
    valu [4]     = valu0 HP.Function
    valu [5]     = valu0 HP.Module
    valu [6]     = valu0 HP.Postulate
    valu [7]     = valu0 HP.Primitive
    valu [8]     = valu0 HP.Record
    valu _       = malformed

instance EmbPrj HP.Aspect where
  icode HP.Comment       = icode0 0
  icode HP.Keyword       = icode0 1
  icode HP.String        = icode0 2
  icode HP.Number        = icode0 3
  icode HP.Symbol        = icode0 4
  icode HP.PrimitiveType = icode0 5
  icode (HP.Name mk b)   = icode2 6 mk b

  value = vcase valu where
    valu [0]        = valu0 HP.Comment
    valu [1]        = valu0 HP.Keyword
    valu [2]        = valu0 HP.String
    valu [3]        = valu0 HP.Number
    valu [4]        = valu0 HP.Symbol
    valu [5]        = valu0 HP.PrimitiveType
    valu [6, mk, b] = valu2 HP.Name mk b
    valu _          = malformed

instance EmbPrj HP.OtherAspect where
  icode HP.Error              = icode0 0
  icode HP.DottedPattern      = icode0 1
  icode HP.UnsolvedMeta       = icode0 2
  icode HP.TerminationProblem = icode0 3
  icode HP.IncompletePattern  = icode0 4

  value = vcase valu where
    valu [0] = valu0 HP.Error
    valu [1] = valu0 HP.DottedPattern
    valu [2] = valu0 HP.UnsolvedMeta
    valu [3] = valu0 HP.TerminationProblem
    valu [4] = valu0 HP.IncompletePattern
    valu _   = malformed

instance EmbPrj HP.MetaInfo where
  icode (HP.MetaInfo a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 HP.MetaInfo a b c d
    valu _            = malformed

instance EmbPrj Precedence where
  icode TopCtx                 = icode0 0
  icode FunctionSpaceDomainCtx = icode0 1
  icode (LeftOperandCtx a)     = icode1 2 a
  icode (RightOperandCtx a)    = icode1 3 a
  icode FunctionCtx            = icode0 4
  icode ArgumentCtx            = icode0 5
  icode InsideOperandCtx       = icode0 6
  icode WithFunCtx             = icode0 7
  icode WithArgCtx             = icode0 8
  icode DotPatternCtx          = icode0 9
  value = vcase valu
    where
    valu [0]    = valu0 TopCtx
    valu [1]    = valu0 FunctionSpaceDomainCtx
    valu [2, a] = valu1 LeftOperandCtx a
    valu [3, a] = valu1 RightOperandCtx a
    valu [4]    = valu0 FunctionCtx
    valu [5]    = valu0 ArgumentCtx
    valu [6]    = valu0 InsideOperandCtx
    valu [7]    = valu0 WithFunCtx
    valu [8]    = valu0 WithArgCtx
    valu [9]    = valu0 DotPatternCtx
    valu _      = malformed

instance EmbPrj ScopeInfo where
  icode (ScopeInfo a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 ScopeInfo a b c d
                           valu _            = malformed

instance EmbPrj Interface where
  icode (Interface a b c d e f g h i) = icode9' a b c d e f g h i
  value = vcase valu where valu [a, b, c, d, e, f, g, h, i] = valu9 Interface a b c d e f g h i
                           valu _                           = malformed



icodeX :: (Dict -> HashTable k Int32) -> (Dict -> IORef Int32) ->
          k -> S Int32
icodeX dict counter key = do
  d     <- asks dict
  c     <- asks counter
  fresh <- lift $ readIORef c
  mi    <- lift $ H.lookup d key
  case mi of
    Just i  -> return i
    Nothing -> do lift $ H.insert d key fresh
                  lift $ writeIORef c (fresh + 1)
                  return fresh

icodeN = icodeX nodeD nodeC

vcase :: forall a . EmbPrj a => (Node -> R a) -> Int32 -> R a
vcase valu ix = do
    memo <- gets nodeMemo
    (aTyp, maybeU) <- liftIO $ do
      aTyp   <- typeRepKey $ typeOf (undefined :: a)
      -- The following tests try to ensure that conversion to Int32
      -- won't truncate the key. The tests can perhaps give erroneous
      -- results if Int is "larger" than Int64.
      when ((convert aTyp :: Int64) > convert (maxBound :: Int32)) __IMPOSSIBLE__
      when ((convert aTyp :: Int64) < convert (minBound :: Int32)) __IMPOSSIBLE__
      let aTyp' = convert aTyp :: Int32
      maybeU <- H.lookup memo (ix, aTyp')
      return (aTyp', maybeU)
    case maybeU of
      Just (U u) -> maybe malformed return (cast u)
      Nothing    -> do
          v <- valu . (! ix) =<< gets nodeE
          liftIO $ H.insert memo (ix, aTyp) (U v)
          return v
    where
    convert :: (Integral b, Integral c) => b -> c
    convert = fromInteger . toInteger

icode0  tag                       = icodeN [tag]
icode1  tag a                     = icodeN . (tag :) =<< sequence [icode a]
icode2  tag a b                   = icodeN . (tag :) =<< sequence [icode a, icode b]
icode3  tag a b c                 = icodeN . (tag :) =<< sequence [icode a, icode b, icode c]
icode4  tag a b c d               = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d]
icode5  tag a b c d e             = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6  tag a b c d e f           = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7  tag a b c d e f g         = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8  tag a b c d e f g h       = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9  tag a b c d e f g h i     = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10 tag a b c d e f g h i j   = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]
icode11 tag a b c d e f g h i j k = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k]

icode0'                        = icodeN []
icode1'  a                     = icodeN =<< sequence [icode a]
icode2'  a b                   = icodeN =<< sequence [icode a, icode b]
icode3'  a b c                 = icodeN =<< sequence [icode a, icode b, icode c]
icode4'  a b c d               = icodeN =<< sequence [icode a, icode b, icode c, icode d]
icode5'  a b c d e             = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6'  a b c d e f           = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7'  a b c d e f g         = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8'  a b c d e f g h       = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9'  a b c d e f g h i     = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10' a b c d e f g h i j   = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]
icode11' a b c d e f g h i j k = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k]

valu0  z                       = return z
valu1  z a                     = valu0 z                      `ap` value a
valu2  z a b                   = valu1 z a                    `ap` value b
valu3  z a b c                 = valu2 z a b                  `ap` value c
valu4  z a b c d               = valu3 z a b c                `ap` value d
valu5  z a b c d e             = valu4 z a b c d              `ap` value e
valu6  z a b c d e f           = valu5 z a b c d e            `ap` value f
valu7  z a b c d e f g         = valu6 z a b c d e f          `ap` value g
valu8  z a b c d e f g h       = valu7 z a b c d e f g        `ap` value h
valu9  z a b c d e f g h i     = valu8 z a b c d e f g h      `ap` value i
valu10 z a b c d e f g h i j   = valu9 z a b c d e f g h i    `ap` value j
valu11 z a b c d e f g h i j k = valu10 z a b c d e f g h i j `ap` value k

-- | Creates an empty dictionary.

emptyDict :: SourceToModule
             -- ^ Maps file names to the corresponding module names.
             -- Must contain a mapping for every file name that is
             -- later encountered.
          -> IO Dict
emptyDict fileMod = Dict
  <$> H.new (==) hashNode
  <*> H.new (==) H.hashString
  <*> H.new (==) (H.hashInt . fromIntegral)
  <*> H.new (==) (H.hashInt . floor)
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> return fileMod

hashNode :: Node -> Int32
hashNode is = List.foldl' f golden is
   where f m c = fromIntegral c * magic + hashInt32 m
         magic  = 0xdeadbeef
         golden :: Int32
         golden = 1013904242
         hashInt32 x = mulHi x golden + x
         mulHi :: Int32 -> Int32 -> Int32
         mulHi a b = fromIntegral (r `shiftR` 32)
             where r :: Int64
                   r = fromIntegral a * fromIntegral b

hashInt2 :: (Int32, Int32) -> Int32
hashInt2 (ix, rep) = hashNode [ix , rep]
