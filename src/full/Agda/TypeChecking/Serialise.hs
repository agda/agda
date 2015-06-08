{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- Andreas, Makoto, Francesco 2014-10-15 AIM XX:
-- -O2 does not have any noticable effect on runtime
-- but sabotages cabal repl with -Werror
-- (due to a conflict with --interactive warning)
-- {-# OPTIONS_GHC -O2                      #-}

-- | Structure-sharing serialisation of Agda interface files.

-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-
-- NOTE: Every time the interface format is changed the interface
-- version number should be bumped _in the same patch_.
-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-

module Agda.TypeChecking.Serialise
  ( encode, encodeFile, encodeInterface
  , decode, decodeFile, decodeInterface, decodeHashes
  , EmbPrj
  )
  where

import Control.Applicative
import Control.Arrow (first, second)
import Control.DeepSeq
import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT, runStateT, gets, modify)
import Data.Array.IArray
import Data.Word
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as L
import Data.Hashable
import qualified Data.HashTable.IO as H
import Data.Int (Int32)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Binary (Binary)
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import qualified Data.List as List
import Data.Function
import Data.Typeable ( cast, Typeable, typeOf, TypeRep )
import qualified Codec.Compression.GZip as G

import GHC.Generics (Generic(..))
import qualified GHC.Generics as Gen
-- , Datatype(..), Constructor(..),
--   C1, D1, K1, M1, S1, NoSelector, Rec0)

import qualified Agda.Compiler.Epic.Interface as Epic

import Agda.Syntax.Common as Common
import Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Info
import Agda.Syntax.Internal as I
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position as P
-- import Agda.Syntax.Position (Position, Range, noRange)
-- import qualified Agda.Syntax.Position as P
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal
import qualified Agda.Compiler.JS.Syntax as JS
import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP
import Agda.Interaction.FindFile

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
-- import Agda.TypeChecking.Pretty

import Agda.Utils.BiMap (BiMap)
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.HashMap (HashMap)
import Agda.Utils.Hash
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.IORef
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Tuple

import Agda.Utils.Except ( ExceptT, MonadError(throwError), runExceptT )

#include "undefined.h"
import Agda.Utils.Impossible

-- Int32
data D_Int32
data C_Int32

instance Gen.Datatype D_Int32 where
  datatypeName _ = "Int32"
  moduleName   _ = "GHC.Int32"
  -- packageName  _ = "base"

instance Gen.Constructor C_Int32 where
  conName _ = "" -- JPM: I'm not sure this is the right implementation...

instance Generic Int32 where
  type Rep Int32 = Gen.D1 D_Int32 (Gen.C1 C_Int32 (Gen.S1 Gen.NoSelector (Gen.Rec0 Int32)))
  from x = Gen.M1 (Gen.M1 (Gen.M1 (Gen.K1 x)))
  to (Gen.M1 (Gen.M1 (Gen.M1 (Gen.K1 x)))) = x

-- Word64
data D_Word64
data C_Word64

instance Gen.Datatype D_Word64 where
  datatypeName _ = "Word64"
  moduleName   _ = "GHC.Word64"
  -- packageName  _ = "base"

instance Gen.Constructor C_Word64 where
  conName _ = "" -- JPM: I'm not sure this is the right implementation...

instance Generic Word64 where
  type Rep Word64 = Gen.D1 D_Word64 (Gen.C1 C_Word64 (Gen.S1 Gen.NoSelector (Gen.Rec0 Word64)))
  from x = Gen.M1 (Gen.M1 (Gen.M1 (Gen.K1 x)))
  to (Gen.M1 (Gen.M1 (Gen.M1 (Gen.K1 x)))) = x


instance Binary NamePart
instance Binary C.Name
instance Binary NameId
instance Binary AbsolutePath
instance (Generic a, Binary a) => Binary (Position' a)
instance (Generic a, Binary a) => Binary (Interval' a)
instance (Generic a, Binary a) => Binary (Range' a)
instance Binary Associativity
instance (Generic a, Binary a) => Binary (Common.ArgInfo a)
instance (Generic a, Binary a, Generic b, Binary b) => Binary (Common.Arg a b)
instance (Generic a, Binary a, Generic b, Binary b) => Binary (Common.Named a b)
instance Binary GenPart
instance Binary Fixity
instance Binary Fixity'
instance Binary A.Name
instance Binary A.ModuleName
instance Binary A.QName
instance Binary Access
instance Binary CtxId
instance Binary Delayed
instance Binary Epic.Forced
instance Binary Epic.Relevance
instance Binary HP.Aspect
instance Binary HP.NameKind
instance Binary HP.OtherAspect
instance Binary Hiding
instance Binary Induction
instance Binary IsAbstract
instance Binary JS.GlobalId
instance Binary JS.LocalId
instance Binary JS.MemberId
instance Binary KindOfName
instance Binary MutualId
instance Binary NameSpaceId
instance Binary Occurrence
instance Binary Polarity
instance Binary Relevance
instance Binary Big
instance Binary (Ranged RawName)
-- instance Binary A.Expr
-- instance Binary A.LamBinding
-- instance Binary A.LetBinding
-- instance Binary A.Pattern
-- instance Binary A.TypedBinding
-- instance Binary A.TypedBindings
-- instance Binary AbstractModule
-- instance Binary AbstractName
-- instance Binary C.QName
-- instance Binary Clause
-- instance Binary ClauseBody
-- instance Binary CompiledClauses
-- instance Binary CompiledRepresentation
-- instance Binary ConHead
-- instance Binary ConPatternInfo
-- instance Binary Definition
-- instance Binary Defn
-- instance Binary DisplayForm
-- instance Binary DisplayTerm
-- instance Binary Epic.EInterface
-- instance Binary Epic.InjectiveFun
-- instance Binary Epic.Tag
-- instance Binary FunctionInverse
-- instance Binary HP.Aspects
-- instance Binary HP.CompressedFile
-- instance Binary HR.Range
-- instance Binary HaskellExport
-- instance Binary HaskellRepresentation
-- instance Binary Interface
-- instance Binary JS.Exp
-- instance Binary Level
-- instance Binary LevelAtom
-- instance Binary Literal
-- instance Binary LocalVar
-- instance Binary NLPat
-- instance Binary NameSpace
-- instance Binary Pattern
-- instance Binary Permutation
-- instance Binary PlusLevel
-- instance Binary Precedence
-- instance Binary Projection
-- instance Binary RewriteRule
-- instance Binary Scope
-- instance Binary ScopeInfo
-- instance Binary Section
-- instance Binary Signature
-- instance Binary Sort
-- instance Binary Telescope
-- instance Binary Term
-- instance Binary TermHead
-- instance Binary TopLevelModuleName
-- instance Binary Type
-- instance Binary WhyInScope
-- instance Binary (Abs (ClauseBodyF Term))
-- instance Binary (Abs (Tele (Common.Dom Color Type)))
-- instance Binary (Abs Sort)
-- instance Binary (Builtin (String, I.QName))
-- instance Binary (Case CompiledClauses)
-- instance Binary (Common.ArgInfo A.Color)
-- instance Binary (Drop Permutation)
-- instance Binary (Elim' DisplayTerm)
-- instance Binary (Elim' NLPat)
-- instance Binary (HashMap I.QName Definition)
-- instance Binary (Open DisplayForm)
-- instance Binary (Ptr Term)
-- instance Binary (WithHiding I.Name)
-- instance Binary AmbiguousQName
-- instance Binary InteractionId
-- instance Binary NotBlocked
-- instance Binary (Common.Dom Color Type)
-- instance Binary (Elim' Term)
-- instance Binary (IORef Term)
-- instance Binary (WithArity CompiledClauses)
-- instance Binary Agda.Syntax.Info.MetaInfo
-- instance Binary Agda.Syntax.Info.ModuleInfo
-- instance Binary PatInfo
-- instance Binary (Common.ArgInfo Term)
-- instance Binary C.OpenShortHand
-- instance Binary ConPatInfo
-- instance Binary ExprInfo
-- instance Binary LetInfo
-- instance Binary MetaId
-- instance Binary (Abs Type)
-- instance Binary A.ModuleApplication
-- instance Binary C.ImportDirective
-- instance Binary DefInfo

-- | Compatibility with @bytestring < 0.10@ which does not implement
--   @instance NFData@, to support @ghc <= 7.4@.
--
--   Note that we only @deepSeq@ for the purpose of correct benchmarking.
--   Thus, a simply non-forcing @return@ would be a possible implementation.

returnForcedByteString :: Monad m => L.ByteString -> m L.ByteString
#if MIN_VERSION_bytestring(0,10,0)
returnForcedByteString bs = return $!! bs
#else
returnForcedByteString bs = return $! bs
#endif

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20150605 * 10 + 0

-- | Serializable thing.

data Ser
  = ID !ID
  | Ser !ByteString -- ^ Already serialized data (in memory).
  deriving (Typeable, Generic, Eq)

type ID = Int32

-- To use number literals for Ser
instance Num Ser where
  fromInteger   = ID . fromInteger
  ID n + ID m   = ID $ n + m
  _ + _         = __IMPOSSIBLE__
  ID n * ID m   = ID $ n * m
  _ * _         =  __IMPOSSIBLE__
  ID n - ID m   = ID $ n - m
  _ - _         = __IMPOSSIBLE__
  abs (ID n)    = ID (abs n)
  abs _         = __IMPOSSIBLE__
  signum (ID n) = ID (signum n)
  signum _      = __IMPOSSIBLE__

instance Binary Ser
instance Hashable Ser where

-- instance Generic Ser where
--   type Rep Ser = D0 D1Ser (C1 C1_0Ser (S1 NoSelector ID) :+:
--                            C1 C1_1Ser (S1 NoSelector (Rep )
--   from (ID  i) =
--   from (Ser a) =
--   to

-- instance Binary Ser where
--   put (ID  i) = put (0 :: Word8) >> put i
--   put (Ser a) = put (1 :: Word8) >> put a
--   get = do
--     tag :: Word8 <- get
--     case tag of
--       0 -> ID <$> get
--       1 -> Ser <$> get
--       _ -> __IMPOSSIBLE__

-- instance Hashable Ser where
--   -- hashWithSalt salt (ID  i) = hashWithSalt salt $ Left i
--   hashWithSalt salt (Ser a) = hashWithSalt salt $ Right a

-- | Constructor tag (maybe omitted) and argument indices.

type Node = [Ser]


-- | The type of hashtables used in this module.
--
-- A very limited amount of testing indicates that 'H.CuckooHashTable'
-- is somewhat slower than 'H.BasicHashTable', and that
-- 'H.LinearHashTable' and the hashtables from "Data.Hashtable" are
-- much slower.

#if defined(mingw32_HOST_OS) && defined(x86_64_HOST_ARCH)
type HashTable k v = H.CuckooHashTable k v
#else
type HashTable k v = H.BasicHashTable k v
#endif

-- | Structure providing fresh identifiers for hash map
--   and counting hash map hits (i.e. when no fresh identifier required).
data FreshAndReuse = FreshAndReuse
  { farFresh :: !ID -- ^ Number of hash map misses.
  , farReuse :: !ID -- ^ Number of hash map hits.
  }

farEmpty :: FreshAndReuse
farEmpty = FreshAndReuse 0 0

lensFresh :: Lens' ID FreshAndReuse
lensFresh f r = f (farFresh r) <&> \ i -> r { farFresh = i }

lensReuse :: Lens' ID FreshAndReuse
lensReuse f r = f (farReuse r) <&> \ i -> r { farReuse = i }

-- | Two 'A.QName's are equal if their @QNameId@ is equal.
type QNameId = [NameId]

-- | Computing a qualified names composed ID.
qnameId :: A.QName -> QNameId
qnameId (A.QName (A.MName ns) n) = map A.nameId $ n:ns

-- | State of the the encoder.
data Dict = Dict
  -- dictionaries which are serialized
  { nodeD        :: !(HashTable Node    ID) -- ^ Will be reversed and serialized.
  , stringD      :: !(HashTable String  ID) -- ^ Ditto.
  , integerD     :: !(HashTable Integer ID) -- ^ Ditto.
  , doubleD      :: !(HashTable Double  ID) -- ^ Ditto.
  -- dicitionaries which are not serialized, but provide
  -- short cuts to speed up serialization
  , termD        :: !(HashTable (Ptr Term) Ser) -- ^ Shortcut dict.
  -- Andreas, Makoto, AIM XXI
  -- Memoizing A.Name does not buy us much if we already memoize A.QName.
  -- , nameD        :: !(HashTable NameId ID)
  , qnameD       :: !(HashTable QNameId Ser)    -- ^ Shortcut dict.
  , nodeC        :: !(IORef FreshAndReuse)  -- counters for fresh indexes
  , stringC      :: !(IORef FreshAndReuse)
  , integerC     :: !(IORef FreshAndReuse)
  , doubleC      :: !(IORef FreshAndReuse)
  , termC        :: !(IORef FreshAndReuse)
  -- , nameC        :: !(IORef FreshAndReuse)
  , qnameC       :: !(IORef FreshAndReuse)
  , stats        :: !(HashTable String Int)
  , collectStats :: Bool
    -- ^ If @True@ collect in @stats@ the quantities of
    --   calls to @icode@ for each @Typeable a@.
  , fileMod      :: !SourceToModule
  }

-- | Creates an empty dictionary.
emptyDict
  :: Bool
     -- ^ Collect statistics for @icode@ calls?
  -> SourceToModule
     -- ^ Maps file names to the corresponding module names.
     --   Must contain a mapping for every file name that is later encountered.
  -> IO Dict
emptyDict collectStats fileMod = Dict
  <$> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> H.new
  <*> pure collectStats
  <*> pure fileMod

-- | Universal type, wraps everything.
data U    = forall a . Typeable a => U !a

-- | Univeral memo structure, to introduce sharing during decoding
type Memo = HashTable (ID, TypeRep) U    -- (node index, type rep)

-- | State of the decoder.
data St = St
  { nodeE     :: !(Array ID Node)
  , stringE   :: !(Array ID String)
  , integerE  :: !(Array ID Integer)
  , doubleE   :: !(Array ID Double)
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

type R a = ExceptT TypeError (StateT St IO) a

-- | Throws an error which is suitable when the data stream is
-- malformed.

malformed :: R a
malformed = throwError $ GenericError "Malformed input."

class Typeable a => EmbPrj a where
  icode :: a -> S Ser  -- ^ Serialization (wrapper).
  icod_ :: a -> S Ser  -- ^ Serialization (worker).
  value :: Ser -> R a  -- ^ Deserialization.
  -- vcase :: (Node -> R a) -> Ser -> R a

  icode a = do
    tickICode a
    icod_ a

  -- By default, we serialize with Binary, not actively introducing sharing.
  -- This should be used for atomic types like Int and ernumerations.
  default icod_ :: (Generic a, Binary a) => a -> S Ser
  icod_ = return . Ser . B.encode

  default value :: (Generic a, Binary a) => Ser -> R a
  value (Ser a) = safeDecode a
  value _       = malformed

  -- default vcase :: (Generic a, Binary a) => (Node -> R a) -> Ser -> R a
  -- vcase value (Ser

safeDecode :: Binary a => ByteString -> R a
safeDecode = either (const malformed) (return . thd3) . B.decodeOrFail

-- | Increase entry for @a@ in 'stats'.
tickICode :: forall a. Typeable a => a -> S ()
tickICode _ = whenM (asks collectStats) $ do
    let key = "icode " ++ show (typeOf (undefined :: a))
    hmap <- asks stats
    liftIO $ do
      n <- fromMaybe 0 <$> H.lookup hmap key
      H.insert hmap key $! n + 1

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encode :: EmbPrj a => a -> TCM L.ByteString
encode a = do
    collectStats <- hasVerbosity "profile.serialize" 20
    fileMod <- sourceToModule
    newD@(Dict nD sD iD dD _ _ nC sC iC dC tC qnameC stats _ _) <- liftIO $
      emptyDict collectStats fileMod
    root <- liftIO $ runReaderT (icode a) newD
    nL <- benchSort $ l nD
    sL <- benchSort $ l sD
    iL <- benchSort $ l iD
    dL <- benchSort $ l dD
    -- Record reuse statistics.
    verboseS "profile.sharing" 10 $ do
      statistics "pointers" tC
    verboseS "profile.serialize" 10 $ do
      statistics "Integer"  iC
      statistics "String"   sC
      statistics "Double"   dC
      statistics "Node"     nC
      statistics "Shared Term" tC
      statistics "A.QName"  qnameC
    when collectStats $ do
      stats <- Map.fromList . map (second toInteger) <$> do
        liftIO $ H.toList stats
      modifyStatistics $ Map.union stats
    -- Encode hashmaps and root, and compress.
    bits1 <- Bench.billTo [ Bench.Serialization, Bench.BinaryEncode ] $
      returnForcedByteString $ B.encode (root, nL, sL, iL, dL)
    let compressParams = G.defaultCompressParams
          { G.compressLevel    = G.bestSpeed
          , G.compressStrategy = G.huffmanOnlyStrategy
          }
    cbits <- Bench.billTo [ Bench.Serialization, Bench.Compress ] $
      returnForcedByteString $ G.compressWith compressParams bits1
    let x = B.encode currentInterfaceVersion `L.append` cbits
    return x
  where
    l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h
    benchSort = Bench.billTo [Bench.Serialization, Bench.Sort] . liftIO
    statistics :: String -> IORef FreshAndReuse -> TCM ()
    statistics kind ioref = do
      FreshAndReuse fresh reused <- liftIO $ readIORef ioref
      tickN (kind ++ "  (fresh)") $ fromIntegral fresh
      tickN (kind ++ " (reused)") $ fromIntegral reused


-- encode :: EmbPrj a => a -> TCM L.ByteString
-- encode a = do
--     fileMod <- sourceToModule
--     (x, shared, total) <- liftIO $ do
--       newD@(Dict nD sD iD dD _ _ _ _ _ stats _) <- emptyDict fileMod
--       root <- runReaderT (icode a) newD
--       nL <- l nD; sL <- l sD; iL <- l iD; dL <- l dD
--       (shared, total) <- readIORef stats
--       return (B.encode currentInterfaceVersion `L.append`
--               G.compress (B.encode (root, nL, sL, iL, dL)), shared, total)
--     verboseS "profile.sharing" 10 $ do
--       tickN "pointers (reused)" $ fromIntegral shared
--       tickN "pointers" $ fromIntegral total
--     return x
--   where
--   l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h

-- | Data.Binary.runGetState is deprecated in favour of runGetIncremental.
--   Reimplementing it in terms of the new function. The new Decoder type contains
--   strict byte strings so we need to be careful not to feed the entire lazy byte
--   string to the decoder at once.
runGetState :: B.Get a -> L.ByteString -> B.ByteOffset -> (a, L.ByteString, B.ByteOffset)
runGetState g s n = feed (B.runGetIncremental g) (L.toChunks s)
  where
    feed (B.Done s n' x) ss     = (x, L.fromChunks (s : ss), n + n')
    feed (B.Fail _ _ err) _     = error err
    feed (B.Partial f) (s : ss) = feed (f $ Just s) ss
    feed (B.Partial f) []       = feed (f Nothing) []

-- | Decodes something. The result depends on the include path.
--
-- Returns 'Nothing' if the input does not start with the right magic
-- number or some other decoding error is encountered.

decode :: EmbPrj a => L.ByteString -> TCM (Maybe a)
decode s = do
  mf   <- use stModuleToSource
  incs <- getIncludeDirs

  -- Note that B.runGetState and G.decompress can raise errors if the
  -- input is malformed. The decoder is (intended to be) strict enough
  -- to ensure that all such errors can be caught by the handler here.

  (mf, r) <- liftIO $ E.handle (\(E.ErrorCall s) -> noResult s) $ do

    (ver, s, _) <- return $ runGetState B.get s 0
    if ver /= currentInterfaceVersion
     then noResult "Wrong interface version."
     else do

      ((r, nL, sL, iL, dL), s, _) <-
        return $ runGetState B.get (G.decompress s) 0
      if s /= L.empty
         -- G.decompress seems to throw away garbage at the end, so
         -- the then branch is possibly dead code.
       then noResult "Garbage at end."
       else do

        st <- St (ar nL) (ar sL) (ar iL) (ar dL)
                <$> liftIO H.new
                <*> return mf <*> return incs
        (r, st) <- runStateT (runExceptT (value r)) st
        return (Just (modFile st), r)

  case mf of
    Nothing -> return ()
    Just mf -> stModuleToSource .= mf

  case r of
    Right x   -> return (Just x)
    Left  err -> do
      reportSLn "import.iface" 5 $ "Error when decoding interface file"
      -- Andreas, 2014-06-11 deactivated debug printing
      -- in order to get rid of dependency of Serialize on TCM.Pretty
      -- reportSDoc "import.iface" 5 $
      --   text "Error when decoding interface file:"
      --   $+$ nest 2 (prettyTCM err)
      return Nothing

  where
  ar l = listArray (0, List.genericLength l - 1) l

  noResult s = return (Nothing, Left $ GenericError s)

encodeInterface :: Interface -> TCM L.ByteString
encodeInterface i = L.append hashes <$> encode i
  where
    hashes :: L.ByteString
    hashes = B.runPut $ B.put (iSourceHash i) >> B.put (iFullHash i)

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encodeFile :: FilePath -> Interface -> TCM ()
encodeFile f i = liftIO . L.writeFile f =<< encodeInterface i

-- | Decodes something. The result depends on the include path.
--
-- Returns 'Nothing' if the file does not start with the right magic
-- number or some other decoding error is encountered.

decodeInterface :: L.ByteString -> TCM (Maybe Interface)
decodeInterface s = decode $ L.drop 16 s

decodeHashes :: L.ByteString -> Maybe (Hash, Hash)
decodeHashes s
  | L.length s < 16 = Nothing
  | otherwise       = Just $ B.runGet getH $ L.take 16 s
  where getH = (,) <$> B.get <*> B.get

decodeFile :: FilePath -> TCM (Maybe Interface)
decodeFile f = decodeInterface =<< liftIO (L.readFile f)

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} EmbPrj String where
#else
instance EmbPrj String where
#endif
  icod_   = ID <.> icodeString
  value (ID i) = (! i) `fmap` gets stringE
  value _      = malformed

instance EmbPrj Integer where
  icod_   = ID <.> icodeInteger
  value (ID i) = (! i) `fmap` gets integerE
  value _      = malformed

instance EmbPrj Word64 where

instance EmbPrj Int32 where

instance EmbPrj Int where

instance EmbPrj Char where

instance EmbPrj Double where

instance EmbPrj () where

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icod_ (a, b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 (,) a b
                           valu _      = malformed

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icod_ (a, b, c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 (,,) a b c
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Maybe a) where
  icod_ Nothing  = icode0'
  icod_ (Just x) = icode1' x
  value = vcase valu where valu []  = valu0 Nothing
                           valu [x] = valu1 Just x
                           valu _   = malformed

instance EmbPrj Bool where

instance EmbPrj AbsolutePath where
  icod_ file = do
    mm <- Map.lookup file <$> asks fileMod
    case mm of
      Just m  -> icode m
      Nothing -> __IMPOSSIBLE__
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

instance EmbPrj Position where
  icod_ (P.Pn file pos line col) = icode4' file pos line col
  value = vcase valu
    where
    valu [f, p, l, c] = valu4 P.Pn f p l c
    valu _            = malformed

instance EmbPrj TopLevelModuleName where
  icod_ (TopLevelModuleName a) = icode1' a
  value = vcase valu where valu [a] = valu1 TopLevelModuleName a
                           valu _   = malformed

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
#else
instance EmbPrj a => EmbPrj [a] where
#endif
  icod_ xs = icodeN =<< mapM icode xs
  value    = vcase (mapM value)

instance (Ord a, Ord b, EmbPrj a, EmbPrj b) => EmbPrj (BiMap a b) where
  icod_ m = icode (BiMap.toList m)
  value m = BiMap.fromList <$> value m

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icod_ m = icode (Map.toList m)
  value m = Map.fromList `fmap` value m

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icod_ s = icode (Set.toList s)
  value s = Set.fromList `fmap` value s

instance EmbPrj P.Interval where
  icod_ (P.Interval p q) = icode2' p q
  value = vcase valu where valu [p, q] = valu2 P.Interval p q
                           valu _      = malformed

instance EmbPrj Range where
  icod_ (P.Range is) = icode1' is
  value = vcase valu where valu [is] = valu1 P.Range is
                           valu _    = malformed

instance EmbPrj HR.Range where
  icod_ (HR.Range a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 HR.Range a b
                           valu _      = malformed

instance EmbPrj C.Name where
  icod_ (C.NoName a b) = icode2 0 a b
  icod_ (C.Name r xs)  = icode2' r xs
  value = vcase valu where valu [0, a, b] = valu2 C.NoName a b
                           valu [r, xs]   = valu2 C.Name   r xs
                           valu _         = malformed

instance EmbPrj NamePart where
  icod_ Hole   = icode0'
  icod_ (Id a) = icode1' a
  value = vcase valu where valu []  = valu0 Hole
                           valu [a] = valu1 Id a
                           valu _   = malformed

instance EmbPrj C.QName where
  icod_ (Qual    a b) = icode2' a b
  icod_ (C.QName a  ) = icode1' a
  value = vcase valu where valu [a, b] = valu2 Qual    a b
                           valu [a]    = valu1 C.QName a
                           valu _      = malformed

instance EmbPrj Scope where
  icod_ (Scope a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Scope a b c d e
                           valu _               = malformed

instance EmbPrj NameSpaceId where

instance EmbPrj Access where

instance EmbPrj NameSpace where
  icod_ (NameSpace a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameSpace a b
                           valu _      = malformed

instance EmbPrj WhyInScope where
  icod_ Defined       = icode0'
  icod_ (Opened a b)  = icode2 0 a b
  icod_ (Applied a b) = icode2 1 a b
  value = vcase valu where valu []        = valu0 Defined
                           valu [0, a, b] = valu2 Opened a b
                           valu [1, a, b] = valu2 Applied a b
                           valu _         = malformed

instance EmbPrj AbstractName where
  icod_ (AbsName a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 AbsName a b c
                           valu _         = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 AbsModule a b
                           valu _      = malformed

instance EmbPrj KindOfName where

instance EmbPrj Agda.Syntax.Fixity.Associativity where

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icod_ (Fixity a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Fixity a b c
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity' where
  icod_ (Fixity' a b) = icode2' a b
  value = vcase valu where valu [a,b] = valu2 Fixity' a b
                           valu _ = malformed

instance EmbPrj GenPart where
  icod_ (BindHole a)   = icode1 0 a
  icod_ (NormalHole a) = icode1 1 a
  icod_ (IdPart a)     = icode1' a
  value = vcase valu where valu [0, a] = valu1 BindHole a
                           valu [1, a] = valu1 NormalHole a
                           valu [a]    = valu1 IdPart a
                           valu _      = malformed

instance EmbPrj A.QName where
  icod_ n@(A.QName a b) = icodeMemo qnameD qnameC (qnameId n) $ icode2' a b
  value = vcase valu where valu [a, b] = valu2 A.QName a b
                           valu _      = malformed

instance EmbPrj A.AmbiguousQName where
  icod_ (A.AmbQ a) = icode a
  value n = A.AmbQ `fmap` value n

instance EmbPrj A.ModuleName where
  icod_ (A.MName a) = icode a
  value n = A.MName `fmap` value n

instance EmbPrj A.Name where
  -- icod_ (A.Name a b c d) = icodeMemo nameD nameC a $ icode4' a b c d
  icod_ (A.Name a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 A.Name a b c d
                           valu _            = malformed

instance (EmbPrj s, EmbPrj t) => EmbPrj (Named s t) where
  icod_ (Named a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Named a b
                           valu _      = malformed

instance EmbPrj a => EmbPrj (Ranged a) where
  icod_ (Ranged r x) = icode2' r x
  value = vcase valu where valu [r, x] = valu2 Ranged r x
                           valu _      = malformed

instance EmbPrj LocalVar where
  icod_ (LocalVar a)      = icode1' a
  icod_ (ShadowedVar a b) = icode2' a b
  value = vcase valu where valu [a]    = valu1 LocalVar a
                           valu [a, b] = valu2 ShadowedVar a b
                           valu _      = malformed

-- Only used for pattern synonyms
instance EmbPrj A.Expr where
  icod_ (A.Var n)               = icode1 0 n
  icod_ (A.Def n)               = icode1 1 n
  icod_ (A.Con ns)              = icode1 2 ns
  icod_ (A.Lit l)               = icode1 3 l
  icod_ (A.QuestionMark{})      = icode0 4
  icod_ (A.Underscore _)        = icode0 5
  icod_ (A.App _ a b)           = icode2 6 a b
  icod_ (A.WithApp _ a b)       = icode2 7 a b
  icod_ (A.Lam  _ a b)          = icode2 8 a b
  icod_ (A.AbsurdLam _ a)       = icode1 9 a
  icod_ (A.ExtendedLam _ _ _ _) = __IMPOSSIBLE__
  icod_ (A.Pi   _ a b)          = icode2 11 a b
  icod_ (A.Fun  _ a b)          = icode2 12 a b
  icod_ (A.Set  _ a)            = icode1 13 a
  icod_ (A.Prop _)              = icode0 14
  icod_ (A.Let  _ _ _)          = __IMPOSSIBLE__
  icod_ (A.ETel a)              = icode1 16 a
  icod_ (A.Rec  _ a)            = icode1 17 a
  icod_ (A.RecUpdate _ a b)     = icode2 18 a b
  icod_ (A.ScopedExpr a b)      = icode2 19 a b
  icod_ (A.QuoteGoal _ a b)     = icode2 20 a b
  icod_ (A.QuoteContext _ a b)  = icode2 21 a b
  icod_ (A.Quote _)             = icode0 22
  icod_ (A.QuoteTerm _)         = icode0 23
  icod_ (A.Unquote _)           = icode0 24
  icod_ (A.DontCare a)          = icode1 25 a
  icod_ (A.PatternSyn a)        = icode1 26 a
  icod_ (A.Proj a)              = icode1 27 a

  value = vcase valu
    where
      valu [0, a]     = valu1 A.Var a
      valu [1, a]     = valu1 A.Def a
      valu [2, a]     = valu1 A.Con a
      valu [3, a]     = valu1 A.Lit a
      valu [4]        = valu0 (A.QuestionMark emptyMetaInfo 0)
      valu [5]        = valu0 (A.Underscore emptyMetaInfo)
      valu [6, a, b]  = valu2 (A.App i) a b
      valu [7, a, b]  = valu2 (A.WithApp i) a b
      valu [8, a, b]  = valu2 (A.Lam i) a b
      valu [9, a]     = valu1 (A.AbsurdLam i) a
      valu [11, a, b] = valu2 (A.Pi i) a b
      valu [12, a, b] = valu2 (A.Fun i) a b
      valu [13, a]    = valu1 (A.Set i) a
      valu [14]       = valu0 (A.Prop i)
      valu [16, a]    = valu1 A.ETel a
      valu [17, a]    = valu1 (A.Rec i) a
      valu [18, a, b] = valu2 (A.RecUpdate i) a b
      valu [19, a, b] = valu2 A.ScopedExpr a b
      valu [20, a, b] = valu2 (A.QuoteGoal i) a b
      valu [21, a, b] = valu2 (A.QuoteContext i) a b
      valu [22]       = valu0 (A.Quote i)
      valu [23]       = valu0 (A.QuoteTerm i)
      valu [24]       = valu0 (A.Unquote i)
      valu [25, a]    = valu1 A.DontCare a
      valu [26, a]    = valu1 A.PatternSyn a
      valu [27, a]    = valu1 A.Proj a
      valu _          = malformed

      i = ExprRange noRange

instance EmbPrj A.Pattern where
  icod_ (A.VarP a)            = icode1 0 a
  icod_ (A.ConP _ a b)        = icode2 1 a b
  icod_ (A.DefP _ a b)        = icode2 2 a b
  icod_ (A.WildP _)           = icode0 3
  icod_ (A.AsP _ a b)         = icode2 4 a b
  icod_ (A.DotP _ a)          = icode1 5 a
  icod_ (A.AbsurdP _)         = icode0 6
  icod_ (A.LitP a)            = icode1 7 a
  icod_ (A.ImplicitP _)       = icode0 8
  icod_ (A.PatternSynP _ a b) = icode2 9 a b

  value = vcase valu
    where
     valu [0, a]    = valu1 A.VarP a
     valu [1, a, b] = valu2 (A.ConP (ConPatInfo False i)) a b
     valu [2, a, b] = valu2 (A.DefP i) a b
     valu [3]       = valu0 (A.WildP i)
     valu [4, a, b] = valu2 (A.AsP i) a b
     valu [5, a]    = valu1 (A.DotP i) a
     valu [6]       = valu0 (A.AbsurdP i)
     valu [7, a]    = valu1 (A.LitP) a
     valu [8]       = valu0 (A.ImplicitP i)
     valu [9, a, b] = valu2 (A.PatternSynP i) a b
     valu _         = malformed

     i = patNoRange

instance EmbPrj A.LamBinding where
  icod_ (A.DomainFree i e) = icode2 0 i e
  icod_ (A.DomainFull a)   = icode1 1 a

  value = vcase valu where valu [0, i, e] = valu2 A.DomainFree i e
                           valu [1, a]    = valu1 A.DomainFull a
                           valu _         = malformed

instance EmbPrj A.LetBinding where
  icod_ (A.LetBind _ a b c d)  = icode4 0 a b c d
  icod_ (A.LetPatBind _ a b )  = icode2 1 a b
  icod_ (A.LetApply _ _ _ _ _) = icode0 2
  icod_ (A.LetOpen _ _)        = icode0 2

  value = vcase valu
    where
      valu [0, a, b, c, d] = valu4 (A.LetBind (LetRange noRange)) a b c d
      valu [1, a, b]       = valu2 (A.LetPatBind (LetRange noRange)) a b
      valu [2]             = throwError $ NotSupported
                                 "importing pattern synonym containing let module"
      valu _               = malformed

instance EmbPrj A.TypedBindings where
  icod_ (A.TypedBindings a b) = icode2' a b

  value = vcase valu where valu [a, b] = valu2 A.TypedBindings a b
                           valu _      = malformed

instance EmbPrj A.TypedBinding where
  icod_ (A.TBind a b c) = icode3 0 a b c
  icod_ (A.TLet a b)    = icode2 1 a b

  value = vcase valu where valu [0, a, b, c] = valu3 A.TBind a b c
                           valu [1, a, b]    = valu2 A.TLet a b
                           valu _            = malformed

instance EmbPrj c => EmbPrj (Common.ArgInfo c) where
  icod_ (ArgInfo h r cs) = icode3' h r cs

  value = vcase valu where valu [h, r, cs] = valu3 ArgInfo h r cs
                           valu _          = malformed

instance EmbPrj NameId where
  icod_ (NameId a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameId a b
                           valu _      = malformed

instance EmbPrj Signature where
  icod_ (Sig a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Sig a b
                           valu _      = malformed

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icod_ m = icode (HMap.toList m)
  value m = HMap.fromList `fmap` value m

instance EmbPrj Section where
  icod_ (Section a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Section a b
                           valu _      = malformed

instance EmbPrj Telescope where
  icod_ EmptyTel        = icode0'
  icod_ (ExtendTel a b) = icode2' a b
  value = vcase valu where valu []     = valu0 EmptyTel
                           valu [a, b] = valu2 ExtendTel a b
                           valu _      = malformed

instance EmbPrj Permutation where
  icod_ (Perm a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Perm a b
                           valu _      = malformed

instance EmbPrj a => EmbPrj (Drop a) where
  icod_ (Drop a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Drop a b
                           valu _      = malformed

instance EmbPrj a => EmbPrj (Elim' a) where
  icod_ (Apply a) = icode1' a
  icod_ (Proj  a) = icode1 0 a
  value = vcase valu where valu [a]    = valu1 Apply a
                           valu [0, a] = valu1 Proj a
                           valu _      = malformed

instance EmbPrj a => EmbPrj (WithHiding a) where
  icod_ (WithHiding a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 WithHiding a b
                           valu _      = malformed

instance (EmbPrj a, EmbPrj c) => EmbPrj (Common.Arg c a) where
  icod_ (Arg i e) = icode2' i e
  value = vcase valu where valu [i, e] = valu2 Arg i e
                           valu _      = malformed

instance (EmbPrj a, EmbPrj c) => EmbPrj (Common.Dom c a) where
  icod_ (Dom i e) = icode2' i e
  value = vcase valu where valu [i, e] = valu2 Dom i e
                           valu _      = malformed

instance EmbPrj Common.Induction where

instance EmbPrj Common.Hiding where

instance EmbPrj Common.Relevance where

instance EmbPrj I.ConHead where
  icod_ (ConHead a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 ConHead a b c
                           valu _         = malformed

instance EmbPrj I.Type where
  icod_ (El a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 El a b
                           valu _      = malformed

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icod_ (NoAbs a b) = icode2 0 a b
  icod_ (Abs a b)   = icode2' a b
  value = vcase valu where valu [a, b]    = valu2 Abs a b
                           valu [0, a, b] = valu2 NoAbs a b
                           valu _         = malformed

instance EmbPrj I.Term where
  icod_ (Var      a b) = icode2 0 a b
  icod_ (Lam      a b) = icode2 1 a b
  icod_ (Lit      a  ) = icode1 2 a
  icod_ (Def      a b) = icode2 3 a b
  icod_ (Con      a b) = icode2 4 a b
  icod_ (Pi       a b) = icode2 5 a b
  icod_ (Sort     a  ) = icode1 7 a
  icod_ (MetaV    a b) = __IMPOSSIBLE__
  icod_ ExtLam{}       = __IMPOSSIBLE__
  icod_ (DontCare a  ) = icode1 8 a
  icod_ (Level    a  ) = icode1 9 a
  icod_ (Shared p)     = icodeMemo termD termC p $ icode (derefPtr p)

  value r = vcase valu' r
    where
      valu' xs = shared <$> valu xs
      valu [0, a, b] = valu2 Var   a b
      valu [1, a, b] = valu2 Lam   a b
      valu [2, a]    = valu1 Lit   a
      valu [3, a, b] = valu2 Def   a b
      valu [4, a, b] = valu2 Con   a b
      valu [5, a, b] = valu2 Pi    a b
      valu [7, a]    = valu1 Sort  a
      valu [8, a]    = valu1 DontCare a
      valu [9, a]    = valu1 Level a
      valu _         = malformed

instance EmbPrj Level where
  icod_ (Max a) = icode1' a
  value = vcase valu where valu [a] = valu1 Max a
                           valu _   = malformed

instance EmbPrj PlusLevel where
  icod_ (ClosedLevel a) = icode1' a
  icod_ (Plus a b)      = icode2' a b
  value = vcase valu where valu [a]    = valu1 ClosedLevel a
                           valu [a, b] = valu2 Plus a b
                           valu _      = malformed

instance EmbPrj LevelAtom where
  icod_ (NeutralLevel _ a) = icode1' a
  icod_ (UnreducedLevel a) = icode1 1 a
  icod_ MetaLevel{}        = __IMPOSSIBLE__
  icod_ BlockedLevel{}     = __IMPOSSIBLE__
  value = vcase valu where
    valu [a]    = valu1 UnreducedLevel a -- we forget that we are a NeutralLevel,
                                         -- since we do not want do (de)serialize
                                         -- the reason for neutrality
    valu [1, a] = valu1 UnreducedLevel a
    valu _      = malformed

instance EmbPrj I.Sort where
  icod_ (Type  a  ) = icode1' a
  icod_ Prop        = icode1 1 ()
  icod_ SizeUniv    = icode1 3 ()
  icod_ Inf         = icode1 4 ()
  icod_ (DLub a b)  = __IMPOSSIBLE__
  value = vcase valu where valu [a]    = valu1 Type  a
                           valu [1, _] = valu0 Prop
                           valu [3, _] = valu0 SizeUniv
                           valu [4, _] = valu0 Inf
                           valu _      = malformed

instance EmbPrj Agda.Syntax.Literal.Literal where
  icod_ (LitInt    a b) = icode2' a b
  icod_ (LitFloat  a b) = icode2 1 a b
  icod_ (LitString a b) = icode2 2 a b
  icod_ (LitChar   a b) = icode2 3 a b
  icod_ (LitQName  a b) = icode2 5 a b
  value = vcase valu where valu [a, b]    = valu2 LitInt    a b
                           valu [1, a, b] = valu2 LitFloat  a b
                           valu [2, a, b] = valu2 LitString a b
                           valu [3, a, b] = valu2 LitChar   a b
                           valu [5, a, b] = valu2 LitQName  a b
                           valu _         = malformed

instance EmbPrj DisplayForm where
  icod_ (Display a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Display a b c
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Open a) where
  icod_ (OpenThing a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 OpenThing a b
                           valu _      = malformed

-- deriving instance EmbPrj CtxId -- newtype  -- nominal representational crap

instance EmbPrj CtxId where

instance EmbPrj DisplayTerm where
  icod_ (DTerm    a  ) = icode1' a
  icod_ (DDot     a  ) = icode1 1 a
  icod_ (DCon     a b) = icode2 2 a b
  icod_ (DDef     a b) = icode2 3 a b
  icod_ (DWithApp a b c) = icode3 4 a b c
  value = vcase valu where valu [a]       = valu1 DTerm a
                           valu [1, a]    = valu1 DDot a
                           valu [2, a, b] = valu2 DCon a b
                           valu [3, a, b] = valu2 DDef a b
                           valu [4, a, b, c] = valu3 DWithApp a b c
                           valu _         = malformed

instance EmbPrj MutualId where -- newtype

instance EmbPrj Definition where
  icod_ (Defn rel a b c d e f g h i j) = icode11' rel a (P.killRange b) c d e f g h i j
  value = vcase valu where valu [rel, a, b, c, d, e, f, g, h, i, j] = valu11 Defn rel a b c d e f g h i j
                           valu _                             = malformed

instance EmbPrj NLPat where
  icod_ (PVar a)   = icode1 0 a
  icod_ (PWild)    = icode0 1
  icod_ (PDef a b) = icode2 2 a b
  icod_ (PTerm a)  = icode1 3 a
  value = vcase valu where valu [0, a]    = valu1 PVar a
                           valu [1]       = valu0 PWild
                           valu [2, a, b] = valu2 PDef a b
                           valu [3, a]    = valu1 PTerm a
                           valu _         = malformed

instance EmbPrj RewriteRule where
  icod_ (RewriteRule a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 RewriteRule a b c d e
                           valu _               = malformed


instance EmbPrj Projection where
  icod_ (Projection a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Projection a b c d e
                           valu _               = malformed

instance EmbPrj HaskellExport where
  icod_ (HsExport a b) = icode2' a b
  value = vcase valu where
    valu [a,b] = valu2 HsExport a b
    valu _ = malformed

instance EmbPrj HaskellRepresentation where
  icod_ (HsType a)   = icode1' a
  icod_ (HsDefn a b) = icode2' a b

  value = vcase valu where
    valu [a]    = valu1 HsType a
    valu [a, b] = valu2 HsDefn a b
    valu _      = malformed

instance EmbPrj JS.Exp where
  icod_ (JS.Self)         = icode0 0
  icod_ (JS.Local i)      = icode1 1 i
  icod_ (JS.Global i)     = icode1 2 i
  icod_ (JS.Undefined)    = icode0 3
  icod_ (JS.String s)     = icode1 4 s
  icod_ (JS.Char c)       = icode1 5 c
  icod_ (JS.Integer n)    = icode1 6 n
  icod_ (JS.Double d)     = icode1 7 d
  icod_ (JS.Lambda n e)   = icode2 8 n e
  icod_ (JS.Object o)     = icode1 9 o
  icod_ (JS.Apply e es)   = icode2 10 e es
  icod_ (JS.Lookup e l)   = icode2 11 e l
  icod_ (JS.If e f g)     = icode3 12 e f g
  icod_ (JS.BinOp e op f) = icode3 13 e op f
  icod_ (JS.PreOp op e)   = icode2 14 op e
  icod_ (JS.Const i)      = icode1 15 i
  value = vcase valu where valu [0]           = valu0 JS.Self
                           valu [1,  a]       = valu1 JS.Local a
                           valu [2,  a]       = valu1 JS.Global a
                           valu [3]           = valu0 JS.Undefined
                           valu [4,  a]       = valu1 JS.String a
                           valu [5,  a]       = valu1 JS.Char a
                           valu [6,  a]       = valu1 JS.Integer a
                           valu [7,  a]       = valu1 JS.Double a
                           valu [8,  a, b]    = valu2 JS.Lambda a b
                           valu [9,  a]       = valu1 JS.Object a
                           valu [10, a, b]    = valu2 JS.Apply a b
                           valu [11, a, b]    = valu2 JS.Lookup a b
                           valu [12, a, b, c] = valu3 JS.If a b c
                           valu [13, a, b, c] = valu3 JS.BinOp a b c
                           valu [14, a, b]    = valu2 JS.PreOp a b
                           valu [15, a]       = valu1 JS.Const a
                           valu _             = malformed

instance EmbPrj JS.LocalId  where -- newtype
instance EmbPrj JS.GlobalId where -- newtype
instance EmbPrj JS.MemberId where -- newtype

instance EmbPrj Polarity where

instance EmbPrj Occurrence where

instance EmbPrj CompiledRepresentation where
  icod_ (CompiledRep a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 CompiledRep a b c d
                           valu _         = malformed

instance EmbPrj Defn where
  icod_ Axiom                                   = icode0 0
  icod_ (Function    a b c d e f g h i j k l m) = icode13 1 a b c d e f g h i j k l m
  icod_ (Datatype    a b c d e f g h i j)       = icode10 2 a b c d e f g h i j
  icod_ (Record      a b c d e f g h i j k l)   = icode12 3 a b c d e f g h i j k l
  icod_ (Constructor a b c d e)                 = icode5 4 a b c d e
  icod_ (Primitive   a b c d)                   = icode4 5 a b c d
  value = vcase valu where
    valu [0]                                     = valu0 Axiom
    valu [1, a, b, c, d, e, f, g, h, i, j, k, l, m] = valu13 Function a b c d e f g h i j k l m
    valu [2, a, b, c, d, e, f, g, h, i, j]       = valu10 Datatype a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h, i, j, k, l] = valu12 Record  a b c d e f g h i j k l
    valu [4, a, b, c, d, e]                      = valu5 Constructor a b c d e
    valu [5, a, b, c, d]                         = valu4 Primitive   a b c d
    valu _                                       = malformed

instance EmbPrj a => EmbPrj (WithArity a) where
  icod_ (WithArity a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 WithArity a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Case a) where
  icod_ (Branches a b c) = icode3' a b c

  value = vcase valu where
    valu [a, b, c] = valu3 Branches a b c
    valu _         = malformed

instance EmbPrj CompiledClauses where
  icod_ Fail       = icode0'
  icod_ (Done a b) = icode2' a (P.killRange b)
  icod_ (Case a b) = icode2 2 a b

  value = vcase valu where
    valu []        = valu0 Fail
    valu [a, b]    = valu2 Done a b
    valu [2, a, b] = valu2 Case a b
    valu _         = malformed

instance EmbPrj FunctionInverse where
  icod_ NotInjective = icode0'
  icod_ (Inverse a)  = icode1' a
  value = vcase valu where valu []  = valu0 NotInjective
                           valu [a] = valu1 Inverse a
                           valu _   = malformed

instance EmbPrj TermHead where
  icod_ SortHead     = icode0'
  icod_ PiHead       = icode0 1
  icod_ (ConsHead a) = icode1 2 a
  value = vcase valu where valu []     = valu0 SortHead
                           valu [1]    = valu0 PiHead
                           valu [2, a] = valu1 ConsHead a
                           valu _      = malformed

instance EmbPrj Common.IsAbstract where

instance EmbPrj I.Clause where
  icod_ (Clause a b c d e f) = icode6' a b c d e f
  value = vcase valu where valu [a, b, c, d, e, f] = valu6 Clause a b c d e f
                           valu _                  = malformed

instance EmbPrj I.ClauseBody where
  icod_ (Body   a) = icode1 0 a
  icod_ (Bind   a) = icode1' a
  icod_ NoBody     = icode0'
  value = vcase valu where valu [0, a] = valu1 Body   a
                           valu [a]    = valu1 Bind   a
                           valu []     = valu0 NoBody
                           valu _      = malformed

instance EmbPrj Delayed where

instance EmbPrj I.ConPatternInfo where
  icod_ (ConPatternInfo a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 ConPatternInfo a b
                           valu _      = malformed

instance EmbPrj I.Pattern where
  icod_ (VarP a    ) = icode1' a
  icod_ (ConP a b c) = icode3' a b c
  icod_ (LitP a    ) = icode1 2 a
  icod_ (DotP a    ) = icode1 3 a
  icod_ (ProjP a   ) = icode1 4 a
  value = vcase valu where valu [a]       = valu1 VarP a
                           valu [a, b, c] = valu3 ConP a b c
                           valu [2, a]    = valu1 LitP a
                           valu [3, a]    = valu1 DotP a
                           valu [4, a]    = valu1 ProjP a
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icod_ (Prim    a) = icode1' a
  icod_ (Builtin a) = icode1 1 a
  value = vcase valu where valu [a]    = valu1 Prim    a
                           valu [1, a] = valu1 Builtin a
                           valu _      = malformed

instance EmbPrj HP.NameKind where

instance EmbPrj HP.Aspect where

instance EmbPrj HP.OtherAspect where

instance EmbPrj HP.Aspects where
  icod_ (HP.Aspects a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 HP.Aspects a b c d
    valu _            = malformed

instance EmbPrj Precedence where
  icod_ TopCtx                 = icode0'
  icod_ FunctionSpaceDomainCtx = icode0 1
  icod_ (LeftOperandCtx a)     = icode1 2 a
  icod_ (RightOperandCtx a)    = icode1 3 a
  icod_ FunctionCtx            = icode0 4
  icod_ ArgumentCtx            = icode0 5
  icod_ InsideOperandCtx       = icode0 6
  icod_ WithFunCtx             = icode0 7
  icod_ WithArgCtx             = icode0 8
  icod_ DotPatternCtx          = icode0 9
  value = vcase valu
    where
    valu []     = valu0 TopCtx
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
  icod_ (ScopeInfo a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 ScopeInfo a b c d
                           valu _            = malformed

instance EmbPrj HP.CompressedFile where
  icod_ (HP.CompressedFile f) = icode1' f
  value = vcase valu
    where
    valu [f] = valu1 HP.CompressedFile f
    valu _   = malformed

instance EmbPrj Interface where
  icod_ (Interface a b c d e f g h i j k) = icode11' a b c d e f g h i j k
  value = vcase valu
    where
      valu [a, b, c, d, e, f, g, h, i, j, k] = valu11 Interface a b c d e f g h i j k
      valu _                                 = malformed

-- This is used for the Epic compiler backend
instance EmbPrj Epic.EInterface where
  icod_ (Epic.EInterface a b c d e f g h) = icode8' a b c d e f g h
  value = vcase valu where
    valu [a, b, c, d, e, f, g, h] = valu8 Epic.EInterface a b c d e f g h
    valu _                        = malformed

instance EmbPrj Epic.InjectiveFun where
  icod_ (Epic.InjectiveFun a b) = icode2' a b
  value = vcase valu where
     valu [a,b] = valu2 Epic.InjectiveFun a b
     valu _     = malformed

instance EmbPrj Epic.Relevance where

instance EmbPrj Epic.Forced where

instance EmbPrj Epic.Tag where
  icod_ (Epic.Tag a)     = icode1 0 a
  icod_ (Epic.PrimTag a) = icode1 1 a
  value = vcase valu
    where
    valu [0, a] = valu1 Epic.Tag a
    valu [1, a] = valu1 Epic.PrimTag a
    valu _      = malformed

-- Specializing icodeX leads to Warning like
-- src/full/Agda/TypeChecking/Serialise.hs:1297:1: Warning:
--     RULE left-hand side too complicated to desugar
--       case cobox_aQY5 of _ [Occ=Dead] { ghc-prim:GHC.Types.Eq# cobox ->
--       icodeX @ String $dEq_aQY3 $dHashable_aQY4
--       }
--
-- type ICodeX k
--   =  (Dict -> HashTable k Int32)
--   -> (Dict -> IORef Int32)
--   -> k -> S Int32
-- {-# SPECIALIZE icodeX :: ICodeX String  #-}
-- {-# SPECIALIZE icodeX :: ICodeX Integer #-}
-- {-# SPECIALIZE icodeX :: ICodeX Double  #-}
-- {-# SPECIALIZE icodeX :: ICodeX Node    #-}

-- Andreas, 2014-10-16 AIM XX:
-- Inlining this increases Serialization time by 10%
-- Makoto's theory: code size increase might lead to
-- instruction cache misses.
-- {-# INLINE icodeX #-}
icodeX :: (Eq k, Hashable k)
  => (Dict -> HashTable k ID)
  -> (Dict -> IORef FreshAndReuse)
  -> k
  -> S ID
icodeX dict counter key = do
  d <- asks dict
  c <- asks counter
  mi <- liftIO $ H.lookup d key
  case mi of
    Just i  -> do
      liftIO $ modifyIORef' c $ over lensReuse (+1)
      return i
    Nothing -> do
      fresh <- (^.lensFresh) <$> do
        liftIO $ readModifyIORef' c $ over lensFresh (+1)
      liftIO $ H.insert d key fresh
      return fresh

-- Instead of inlining icodeX, we manually specialize it to
-- its four uses: Integer, String, Double, Node.
-- Not a great gain (hardly noticeable), but not harmful.

icodeInteger :: Integer -> S ID
icodeInteger key = do
  d <- asks integerD
  c <- asks integerC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

icodeDouble :: Double -> S ID
icodeDouble key = do
  d <- asks doubleD
  c <- asks doubleC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

icodeString :: String -> S ID
icodeString key = do
  d <- asks stringD
  c <- asks stringC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

icodeN :: Node -> S Ser
icodeN key = ID <$> do
  d <- asks nodeD
  c <- asks nodeC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

-- icodeN :: [Int32] -> S Int32
-- icodeN = icodeX nodeD nodeC

-- | Shortcut: @icode@ only if thing has not seen before.
icodeMemo
  :: (Eq a, Ord a, Hashable a)
  => (Dict -> HashTable a Ser)    -- ^ Memo structure for thing of key @a@.
  -> (Dict -> IORef FreshAndReuse)  -- ^ Statistics.
  -> a        -- ^ Key to the thing.
  -> S Ser  -- ^ Fallback computation to encode the thing.
  -> S Ser  -- ^ Encoded thing.
icodeMemo getDict getCounter a icodeP = do
    h  <- asks getDict
    mi <- liftIO $ H.lookup h a
    st <- asks getCounter
    case mi of
      Just i  -> liftIO $ do
        modifyIORef' st $ over lensReuse (+ 1)
        return i
      Nothing -> do
        liftIO $ modifyIORef' st $ over lensFresh (+1)
        i <- icodeP
        liftIO $ H.insert h a i
        return i

-- {-# INLINE vcase #-}
-- | @vcase value ix@ decodes thing represented by @ix :: Int32@
--   via the @valu@ function and stores it in 'nodeMemo'.
--   If @ix@ is present in 'nodeMemo', @valu@ is not used, but
--   the thing is read from 'nodeMemo' instead.
vcase :: forall a . (EmbPrj a) => (Node -> R a) -> Ser -> R a
vcase valu (Ser a) = __IMPOSSIBLE__
vcase valu (ID ix) = do
    memo <- gets nodeMemo
    -- compute run-time representation of type a
    let aTyp = typeOf (undefined :: a)
    -- to introduce sharing, see if we have seen a thing
    -- represented by ix before
    maybeU <- liftIO $ H.lookup memo (ix, aTyp)
    case maybeU of
      -- yes, we have seen it before, use the version from memo
      Just (U u) -> maybe malformed return (cast u)
      -- no, it's new, so generate it via valu and insert it into memo
      Nothing    -> do
          v <- valu . (! ix) =<< gets nodeE
          liftIO $ H.insert memo (ix, aTyp) (U v)
          return v

-- Andreas, Makoto, AIM XX (2014-10-15):
-- No performance gain for INLINE here (neutral / slighly negative).
--
-- {-# INLINE icode0 #-}
-- {-# INLINE icode1 #-}
-- {-# INLINE icode2 #-}
-- {-# INLINE icode3 #-}
-- {-# INLINE icode4 #-}
-- {-# INLINE icode5 #-}
-- {-# INLINE icode6 #-}
-- {-# INLINE icode7 #-}
-- {-# INLINE icode8 #-}
-- {-# INLINE icode9 #-}
-- {-# INLINE icode10 #-}
-- {-# INLINE icode11 #-}
-- {-# INLINE icode12 #-}
-- {-# INLINE icode13 #-}
-- {-# INLINE icode14 #-}

type Tag = Ser

icode0 :: Tag -> S Ser

icode1 :: EmbPrj a => Tag -> a -> S Ser

icode2 :: (EmbPrj a, EmbPrj b) =>
          Tag -> a -> b ->
          S Ser

icode3 :: (EmbPrj a, EmbPrj b, EmbPrj c) =>
          Tag -> a -> b -> c ->
          S Ser

icode4 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d) =>
          Tag -> a -> b -> c -> d ->
          S Ser

icode5 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e) =>
          Tag -> a -> b -> c -> d -> e ->
          S Ser

icode6 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f) =>
          Tag -> a -> b -> c -> d -> e -> f ->
          S Ser

icode7 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g ) =>
          Tag -> a -> b -> c -> d -> e -> f -> g ->
          S Ser

icode8 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h ) =>
          Tag -> a -> b -> c -> d -> e -> f -> g -> h ->
          S Ser

icode9 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i ) =>
          Tag -> a -> b -> c -> d -> e -> f -> g -> h -> i ->
          S Ser

icode10 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j ) =>
           Tag -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j ->
           S Ser

icode11 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k ) =>
           Tag -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k ->
           S Ser

icode12 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l ) =>
           Tag -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l ->
           S Ser

icode13 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
           , EmbPrj m ) =>
           Tag -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m ->
           S Ser

icode14 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
           , EmbPrj m, EmbPrj n ) =>
           Tag -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n ->
           S Ser

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
icode12 tag a b c d e f g h i j k l = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l]
icode13 tag a b c d e f g h i j k l m = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m]
icode14 tag a b c d e f g h i j k l m n = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m, icode n]


-- Andreas, Makoto, AIM XX (2014-10-15):
-- No performance gain for INLINE here (neutral / slighly negative).
--
-- {-# INLINE icode0' #-}
-- {-# INLINE icode1' #-}
-- {-# INLINE icode2' #-}
-- {-# INLINE icode3' #-}
-- {-# INLINE icode4' #-}
-- {-# INLINE icode5' #-}
-- {-# INLINE icode6' #-}
-- {-# INLINE icode7' #-}
-- {-# INLINE icode8' #-}
-- {-# INLINE icode9' #-}
-- {-# INLINE icode10' #-}
-- {-# INLINE icode11' #-}
-- {-# INLINE icode12' #-}
-- {-# INLINE icode13' #-}
-- {-# INLINE icode14' #-}

icode0' :: S Ser

icode1' :: EmbPrj a => a -> S Ser

icode2' :: (EmbPrj a, EmbPrj b) =>
           a -> b ->
           S Ser

icode3' :: (EmbPrj a, EmbPrj b, EmbPrj c) =>
           a -> b -> c ->
           S Ser

icode4' :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d) =>
           a -> b -> c -> d ->
           S Ser

icode5' :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e) =>
           a -> b -> c -> d -> e ->
           S Ser

icode6' :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f) =>
           a -> b -> c -> d -> e -> f ->
           S Ser

icode7' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g ) =>
           a -> b -> c -> d -> e -> f -> g ->
           S Ser

icode8' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h ) =>
           a -> b -> c -> d -> e -> f -> g -> h ->
           S Ser

icode9' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i ) =>
           a -> b -> c -> d -> e -> f -> g -> h -> i ->
           S Ser

icode10' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j ->
            S Ser

icode11' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k ->
            S Ser

icode12' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l ->
            S Ser

icode13' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
            , EmbPrj m ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m ->
            S Ser

icode14' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
            , EmbPrj m, EmbPrj n ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n ->
            S Ser

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
icode12' a b c d e f g h i j k l = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l]
icode13' a b c d e f g h i j k l m = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m]
icode14' a b c d e f g h i j k l m n = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m, icode n]

valu0 :: a -> R a

valu1 :: EmbPrj a => (a -> b) -> Ser -> R b

valu2 :: (EmbPrj a, EmbPrj b) =>
         (a -> b -> c) ->
         Ser -> Ser ->
         R c

valu3 :: (EmbPrj a, EmbPrj b, EmbPrj c) =>
         (a -> b -> c -> d) ->
         Ser -> Ser -> Ser ->
         R d

valu4 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d) =>
         (a -> b -> c -> d -> e) ->
         Ser -> Ser -> Ser -> Ser ->
         R e

valu5 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e) =>
         (a -> b -> c -> d -> e -> f) ->
         Ser -> Ser -> Ser -> Ser -> Ser ->
         R f

valu6 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f) =>
         (a -> b -> c -> d -> e -> f -> g) ->
         Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
         R g

valu7 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
         , EmbPrj g ) =>
         (a -> b -> c -> d -> e -> f -> g -> h) ->
         Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
         R h

valu8 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
         , EmbPrj g, EmbPrj h ) =>
         (a -> b -> c -> d -> e -> f -> g -> h -> i) ->
         Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
         R i

valu9 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
         , EmbPrj g, EmbPrj h, EmbPrj i ) =>
         (a -> b -> c -> d -> e -> f -> g -> h -> i -> j) ->
         Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
         R j

valu10 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k) ->
          Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
          R k

valu11 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l) ->
          Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
         R l

valu12 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m) ->
          Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
          R m

valu13 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
          , EmbPrj m ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n) ->
          Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
          R n

valu14 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
          , EmbPrj m, EmbPrj n ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o) ->
          Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser -> Ser ->
          R o

valu0  z                           = return z
valu1  z a                         = valu0 z                        `ap` value a
valu2  z a b                       = valu1 z a                      `ap` value b
valu3  z a b c                     = valu2 z a b                    `ap` value c
valu4  z a b c d                   = valu3 z a b c                  `ap` value d
valu5  z a b c d e                 = valu4 z a b c d                `ap` value e
valu6  z a b c d e f               = valu5 z a b c d e              `ap` value f
valu7  z a b c d e f g             = valu6 z a b c d e f            `ap` value g
valu8  z a b c d e f g h           = valu7 z a b c d e f g          `ap` value h
valu9  z a b c d e f g h i         = valu8 z a b c d e f g h        `ap` value i
valu10 z a b c d e f g h i j       = valu9 z a b c d e f g h i      `ap` value j
valu11 z a b c d e f g h i j k     = valu10 z a b c d e f g h i j   `ap` value k
valu12 z a b c d e f g h i j k l   = valu11 z a b c d e f g h i j k `ap` value l
valu13 z a b c d e f g h i j k l m = valu12 z a b c d e f g h i j k l `ap` value m
valu14 z a b c d e f g h i j k l m n = valu13 z a b c d e f g h i j k l m `ap` value n

-- -}
