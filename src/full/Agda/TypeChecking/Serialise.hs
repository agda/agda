{-# LANGUAGE OverlappingInstances,
             TypeSynonymInstances,
             FlexibleInstances,
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

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Error
import Data.Array.IArray
import Data.Bits (shiftR)
import Data.Word
import Data.ByteString.Lazy as L
import Data.Hashable
import qualified Data.HashTable.IO as H
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

import qualified Agda.Compiler.Epic.Interface as Epic

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Info
import Agda.Syntax.Internal as I
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position (Position, Range, noRange)
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal
import qualified Agda.Compiler.JS.Syntax as JS
import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP
import Agda.Interaction.FindFile

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Pretty
import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap

#include "../undefined.h"
import Agda.Utils.Impossible

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20121012 * 10 + 0

-- | Constructor tag (maybe omitted) and argument indices.

type Node = [Int32]

-- | The type of hashtables used in this module.
--
-- A very limited amount of testing indicates that 'H.CuckooHashTable'
-- is somewhat slower than 'H.BasicHashTable', and that
-- 'H.LinearHashTable' and the hashtables from "Data.Hashtable" are
-- much slower.

type HashTable k v = H.BasicHashTable k v

data Dict = Dict{ nodeD     :: !(HashTable Node    Int32)
                , stringD   :: !(HashTable String  Int32)
                , integerD  :: !(HashTable Integer Int32)
                , doubleD   :: !(HashTable Double  Int32)
                , termD     :: !(HashTable (Ptr Term) Int32)
                , nodeC     :: !(IORef Int32)  -- counters for fresh indexes
                , stringC   :: !(IORef Int32)
                , integerC  :: !(IORef Int32)
                , doubleC   :: !(IORef Int32)
                , sharingStats :: !(IORef (Int32, Int32))
                , fileMod   :: !SourceToModule
                }

data U    = forall a . Typeable a => U !a
type Memo = HashTable (Int32, TypeRep) U    -- (node index, type rep)

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
    (x, shared, total) <- liftIO $ do
      newD@(Dict nD sD iD dD _ _ _ _ _ stats _) <- emptyDict fileMod
      root <- runReaderT (icode a) newD
      nL <- l nD; sL <- l sD; iL <- l iD; dL <- l dD
      (shared, total) <- readIORef stats
      return (B.encode currentInterfaceVersion `L.append`
              G.compress (B.encode (root, nL, sL, iL, dL)), shared, total)
    verboseS "profile.sharing" 10 $ do
      tickN "pointers (reused)" $ fromIntegral shared
      tickN "pointers" $ fromIntegral total
    return x
  where
  l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h

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

  (mf, r) <- liftIO $ E.handle (\(E.ErrorCall s) -> noResult s) $ do

    (ver, s, _) <- return $ B.runGetState B.get s 0
    if ver /= currentInterfaceVersion
     then noResult "Wrong interface version."
     else do

      ((r, nL, sL, iL, dL), s, _) <-
        return $ B.runGetState B.get (G.decompress s) 0
      if s /= L.empty
         -- G.decompress seems to throw away garbage at the end, so
         -- the then branch is possibly dead code.
       then noResult "Garbage at end."
       else do

        st <- St (ar nL) (ar sL) (ar iL) (ar dL)
                <$> liftIO H.new
                <*> return mf <*> return incs
        (r, st) <- runStateT (runErrorT (value r)) st
        return (Just (modFile st), r)

  case mf of
    Nothing -> return ()
    Just mf -> modify $ \s -> s { stModuleToSource = mf }

  case r of
    Right x   -> return (Just x)
    Left  err -> do
      reportSDoc "import.iface" 5 $
        text "Error when decoding interface file:" $+$
        nest 2 (prettyTCM err)
      return Nothing

  where
  ar l = listArray (0, List.genericLength l - 1) l

  noResult s = return (Nothing, Left $ GenericError s)

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

instance EmbPrj () where
  icode () = icode0'
  value = vcase valu where valu [] = valu0 ()
                           valu _  = malformed

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
  icode True  = icode0'
  icode False = icode0 0
  value = vcase valu where valu []  = valu0 True
                           valu [0] = valu0 False
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
  value = vcase (mapM value)
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
  icode (C.Name r xs)  = icode2' r xs
  value = vcase valu where valu [0, a, b] = valu2 C.NoName a b
                           valu [r, xs]   = valu2 C.Name   r xs
                           valu _         = malformed

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
  icode (Scope a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Scope a b c d e
                           valu _            = malformed

instance EmbPrj NameSpaceId where
  icode PublicNS        = icode0'
  icode PrivateNS       = icode0 1
  icode ImportedNS      = icode0 2
  icode OnlyQualifiedNS = icode0 3
  value = vcase valu where valu []  = valu0 PublicNS
                           valu [1] = valu0 PrivateNS
                           valu [2] = valu0 ImportedNS
                           valu [3] = valu0 OnlyQualifiedNS
                           valu _   = malformed

instance EmbPrj Access where
  icode PrivateAccess = icode0 0
  icode PublicAccess  = icode0'
  icode OnlyQualified = icode0 2
  value = vcase valu where valu [0] = valu0 PrivateAccess
                           valu []  = valu0 PublicAccess
                           valu [2] = valu0 OnlyQualified
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
  icode DefName = icode0'
  icode ConName = icode0 1
  icode FldName = icode0 2
  icode PatternSynName = icode0 2
  value = vcase valu where valu []  = valu0 DefName
                           valu [1] = valu0 ConName
                           valu [2] = valu0 FldName
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icode (LeftAssoc  a b) = icode2 0 a b
  icode (RightAssoc a b) = icode2 1 a b
  icode (NonAssoc   a b) = icode2' a b
  value = vcase valu where valu [0, a, b] = valu2 LeftAssoc  a b
                           valu [1, a, b] = valu2 RightAssoc a b
                           valu [a, b]    = valu2 NonAssoc   a b
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity' where
  icode (Fixity' a b) = icode2' a b
  value = vcase valu where valu [a,b] = valu2 Fixity' a b
                           valu _ = malformed

instance EmbPrj GenPart where
    icode (BindHole a)   = icode1 0 a
    icode (NormalHole a) = icode1 1 a
    icode (IdPart a)     = icode1' a
    value = vcase valu where valu [0, a] = valu1 BindHole a
                             valu [1, a] = valu1 NormalHole a
                             valu [a]    = valu1 IdPart a
                             valu _      = malformed

instance EmbPrj A.QName where
  icode (A.QName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 A.QName a b
                           valu _      = malformed

instance EmbPrj A.AmbiguousQName where
  icode (A.AmbQ a) = icode a
  value n = A.AmbQ `fmap` value n

instance EmbPrj A.ModuleName where
  icode (A.MName a) = icode a
  value n = A.MName `fmap` value n

instance EmbPrj A.Name where
  icode (A.Name a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 A.Name a b c d
                           valu _            = malformed

instance (EmbPrj s, EmbPrj t) => EmbPrj (Named s t) where
  icode (Named a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Named a b
                           valu _      = malformed

instance EmbPrj A.Expr where
  icode (A.Var n)               = icode1 0 n
  icode (A.Def n)               = icode1 1 n
  icode (A.Con ns)              = icode1 2 ns
  icode (A.Lit l)               = icode1 3 l
  icode (A.QuestionMark _)      = icode0 4
  icode (A.Underscore _)        = icode0 5
  icode (A.App _ a b)           = icode2 6 a b
  icode (A.WithApp _ a b)       = icode2 7 a b
  icode (A.Lam  _ a b)          = icode2 8 a b
  icode (A.AbsurdLam _ a)       = icode1 9 a
  icode (A.ExtendedLam _ _ _ _) = icode0 10
  icode (A.Pi   _ a b)          = icode2 11 a b
  icode (A.Fun  _ a b)          = icode2 12 a b
  icode (A.Set  _ a)            = icode1 13 a
  icode (A.Prop _)              = icode0 14
  icode (A.Let  _ a b)          = icode2 15 a b
  icode (A.ETel a)              = icode1 16 a
  icode (A.Rec  _ a)            = icode1 17 a
  icode (A.RecUpdate _ a b)     = icode2 18 a b
  icode (A.ScopedExpr a b)      = icode2 19 a b
  icode (A.QuoteGoal _ a b)     = icode2 20 a b
  icode (A.Quote _)             = icode0 21
  icode (A.QuoteTerm _)         = icode0 22
  icode (A.Unquote _)           = icode0 23
  icode (A.DontCare a)          = icode1 24 a
  icode (A.PatternSyn a)        = icode1 25 a

  value = vcase valu
    where
      valu [0, a]     = valu1 A.Var a
      valu [1, a]     = valu1 A.Def a
      valu [2, a]     = valu1 A.Con a
      valu [3, a]     = valu1 A.Lit a
      valu [4]        = valu0 (A.QuestionMark emptyMetaInfo)
      valu [5]        = valu0 (A.Underscore emptyMetaInfo)
      valu [6, a, b]  = valu2 (A.App i) a b
      valu [7, a, b]  = valu2 (A.WithApp i) a b
      valu [8, a, b]  = valu2 (A.Lam i) a b
      valu [9, a]     = valu1 (A.AbsurdLam i) a
      valu [10]       = throwError $ NotSupported
                            "importing pattern synonym containing extended lambda"
      valu [11, a, b] = valu2 (A.Pi i) a b
      valu [12, a, b] = valu2 (A.Fun i) a b
      valu [13, a]    = valu1 (A.Set i) a
      valu [14]       = valu0 (A.Prop i)
      valu [15, a, b] = valu2 (A.Let i) a b
      valu [16, a]    = valu1 A.ETel a
      valu [17, a]    = valu1 (A.Rec i) a
      valu [18, a, b] = valu2 (A.RecUpdate i) a b
      valu [19, a, b] = valu2 A.ScopedExpr a b
      valu [20, a, b] = valu2 (A.QuoteGoal i) a b
      valu [21]       = valu0 (A.Quote i)
      valu [22]       = valu0 (A.QuoteTerm i)
      valu [23]       = valu0 (A.Unquote i)
      valu [24, a]    = valu1 A.DontCare a
      valu [25, a]    = valu1 A.PatternSyn a
      valu _          = malformed

      i = ExprRange noRange

instance EmbPrj A.Pattern where
  icode (A.VarP a)            = icode1 0 a
  icode (A.ConP _ a b)        = icode2 1 a b
  icode (A.DefP _ a b)        = icode2 2 a b
  icode (A.WildP _)           = icode0 3
  icode (A.AsP _ a b)         = icode2 4 a b
  icode (A.DotP _ a)          = icode1 5 a
  icode (A.AbsurdP _)         = icode0 6
  icode (A.LitP a)            = icode1 7 a
  icode (A.ImplicitP _)       = icode0 8
  icode (A.PatternSynP _ a b) = icode2 9 a b

  value = vcase valu
    where
     valu [0, a]    = valu1 A.VarP a
     valu [1, a, b] = valu2 (A.ConP i) a b
     valu [2, a, b] = valu2 (A.DefP i) a b
     valu [3]       = valu0 (A.WildP i)
     valu [4, a, b] = valu2 (A.AsP i) a b
     valu [5, a]    = valu1 (A.DotP i) a
     valu [6]       = valu0 (A.AbsurdP i)
     valu [7, a]    = valu1 (A.LitP) a
     valu [8]       = valu0 (A.ImplicitP i)
     valu [9, a, b] = valu2 (A.PatternSynP i) a b
     valu _         = malformed

     i = PatRange noRange

instance EmbPrj A.LamBinding where
  icode (A.DomainFree a b c) = icode3 0 a b c
  icode (A.DomainFull a)     = icode1 1 a

  value = vcase valu where valu [0, a, b, c] = valu3 A.DomainFree a b c
                           valu [1, a]       = valu1 A.DomainFull a
                           valu _            = malformed

instance EmbPrj A.TypedBindings where
  icode (A.TypedBindings a b) = icode2' a b

  value = vcase valu where valu [a, b] = valu2 A.TypedBindings a b
                           valu _      = malformed

instance EmbPrj A.TypedBinding where
  icode (A.TBind a b c) = icode3 0 a b c
  icode (A.TNoBind a)   = icode1 1 a

  value = vcase valu where valu [0, a, b, c] = valu3 A.TBind a b c
                           valu [1, a]       = valu1 A.TNoBind a
                           valu _            = malformed

instance EmbPrj A.LetBinding where
  icode (A.LetBind _ a b c d)  = icode4 0 a b c d
  icode (A.LetPatBind _ a b )  = icode2 1 a b
  icode (A.LetApply _ _ _ _ _) = icode0 2
  icode (A.LetOpen _ _)        = icode0 2

  value = vcase valu
    where
      valu [0, a, b, c, d] = valu4 (A.LetBind (LetRange noRange)) a b c d
      valu [1, a, b]       = valu2 (A.LetPatBind (LetRange noRange)) a b
      valu [2]             = throwError $ NotSupported
                                 "importing pattern synonym containing let module"
      valu _               = malformed

instance EmbPrj NameId where
  icode (NameId a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameId a b
                           valu _      = malformed

instance EmbPrj Signature where
  icode (Sig a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Sig a b
                           valu _      = malformed

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icode m = icode (HMap.toList m)
  value m = HMap.fromList `fmap` value m

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

instance (EmbPrj a) => EmbPrj (Agda.Syntax.Common.Dom a) where
  icode (Dom a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Dom a b c
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Common.Induction where
  icode Inductive   = icode0'
  icode CoInductive = icode0 1
  value = vcase valu where valu []  = valu0 Inductive
                           valu [1] = valu0 CoInductive
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Common.Hiding where
  icode Hidden    = icode0 0
  icode NotHidden = icode0'
  icode Instance  = icode0 2
  value = vcase valu where valu [0] = valu0 Hidden
                           valu []  = valu0 NotHidden
                           valu [2] = valu0 Instance
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Common.Relevance where
  icode Relevant   = icode0'
  icode Irrelevant = icode0 1
  icode Forced     = icode0 2
  icode NonStrict  = icode0 3
  icode UnusedArg  = icode0 4
  value = vcase valu where valu []  = valu0 Relevant
                           valu [1] = valu0 Irrelevant
                           valu [2] = valu0 Forced
                           valu [3] = valu0 NonStrict
                           valu [4] = valu0 UnusedArg
                           valu _   = malformed

instance EmbPrj I.Type where
  icode (El a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 El a b
                           valu _      = malformed

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icode (NoAbs a b) = icode2 0 a b
  icode (Abs a b)   = icode2' a b
  value = vcase valu where valu [a, b]    = valu2 Abs a b
                           valu [0, a, b] = valu2 NoAbs a b
                           valu _         = malformed

instance EmbPrj I.Term where
  icode (Var      a b) = icode2 0 a b
  icode (Lam      a b) = icode2 1 a b
  icode (Lit      a  ) = icode1 2 a
  icode (Def      a b) = icode2 3 a b
  icode (Con      a b) = icode2 4 a b
  icode (Pi       a b) = icode2 5 a b
  icode (Sort     a  ) = icode1 7 a
  icode (MetaV    a b) = __IMPOSSIBLE__
  icode (DontCare a  ) = icode1 8 a
  icode (Level    a  ) = icode1 9 a
  icode (Shared p)     = do
    h  <- asks termD
    mi <- liftIO $ H.lookup h p
    st <- asks sharingStats
    case mi of
      Just i  -> liftIO $ modifyIORef st (\(a, b) -> ((,) $! a + 1) b) >> return i
      Nothing -> do
        liftIO $ modifyIORef st (\(a, b) -> (,) a $! b + 1)
        n <- icode (derefPtr p)
        liftIO $ H.insert h p n
        return n

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
  icode (Max a) = icode1' a
  value = vcase valu where valu [a] = valu1 Max a
                           valu _   = malformed

instance EmbPrj PlusLevel where
  icode (ClosedLevel a) = icode1' a
  icode (Plus a b)      = icode2' a b
  value = vcase valu where valu [a]    = valu1 ClosedLevel a
                           valu [a, b] = valu2 Plus a b
                           valu _      = malformed

instance EmbPrj LevelAtom where
  icode (NeutralLevel a)   = icode1' a
  icode (UnreducedLevel a) = icode1 1 a
  icode MetaLevel{}        = __IMPOSSIBLE__
  icode BlockedLevel{}     = __IMPOSSIBLE__
  value = vcase valu where valu [a]    = valu1 NeutralLevel a
                           valu [1, a] = valu1 UnreducedLevel a
                           valu _      = malformed

instance EmbPrj I.Sort where
  icode (Type  a  ) = icode1' a
  icode Prop        = icode1 1 ()
  icode Inf         = icode1 4 ()
  icode (DLub a b)  = __IMPOSSIBLE__
  value = vcase valu where valu [a]    = valu1 Type  a
                           valu [1, _] = valu0 Prop
                           valu [4, _] = valu0 Inf
                           valu _      = malformed

instance EmbPrj Agda.Syntax.Literal.Literal where
  icode (LitInt    a b) = icode2' a b
  icode (LitFloat  a b) = icode2 1 a b
  icode (LitString a b) = icode2 2 a b
  icode (LitChar   a b) = icode2 3 a b
  icode (LitQName  a b) = icode2 5 a b
  value = vcase valu where valu [a, b]    = valu2 LitInt    a b
                           valu [1, a, b] = valu2 LitFloat  a b
                           valu [2, a, b] = valu2 LitString a b
                           valu [3, a, b] = valu2 LitChar   a b
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
  icode (DDot     a  ) = icode1 1 a
  icode (DCon     a b) = icode2 2 a b
  icode (DDef     a b) = icode2 3 a b
  icode (DWithApp a b) = icode2 4 a b
  value = vcase valu where valu [a]       = valu1 DTerm a
                           valu [1, a]    = valu1 DDot a
                           valu [2, a, b] = valu2 DCon a b
                           valu [3, a, b] = valu2 DDef a b
                           valu [4, a, b] = valu2 DWithApp a b
                           valu _         = malformed

instance EmbPrj MutualId where
  icode (MutId a) = icode a
  value n = MutId `fmap` value n

instance EmbPrj Definition where
  icode (Defn rel a b c d e f g h) = icode9' rel a (P.killRange b) c d e f g h
  value = vcase valu where valu [rel, a, b, c, d, e, f, g, h] = valu9 Defn rel a b c d e f g h
                           valu _                             = malformed

instance EmbPrj HaskellRepresentation where
  icode (HsType a)   = icode1' a
  icode (HsDefn a b) = icode2' a b

  value = vcase valu where
    valu [a]    = valu1 HsType a
    valu [a, b] = valu2 HsDefn a b
    valu _      = malformed

instance EmbPrj JS.Exp where
  icode (JS.Self)         = icode0 0
  icode (JS.Local i)      = icode1 1 i
  icode (JS.Global i)     = icode1 2 i
  icode (JS.Undefined)    = icode0 3
  icode (JS.String s)     = icode1 4 s
  icode (JS.Char c)       = icode1 5 c
  icode (JS.Integer n)    = icode1 6 n
  icode (JS.Double d)     = icode1 7 d
  icode (JS.Lambda n e)   = icode2 8 n e
  icode (JS.Object o)     = icode1 9 o
  icode (JS.Apply e es)   = icode2 10 e es
  icode (JS.Lookup e l)   = icode2 11 e l
  icode (JS.If e f g)     = icode3 12 e f g
  icode (JS.BinOp e op f) = icode3 13 e op f
  icode (JS.PreOp op e)   = icode2 14 op e
  icode (JS.Const i)      = icode1 15 i
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

instance EmbPrj JS.LocalId where
  icode (JS.LocalId l) = icode l
  value n = JS.LocalId `fmap` value n

instance EmbPrj JS.GlobalId where
  icode (JS.GlobalId l) = icode l
  value n = JS.GlobalId `fmap` value n

instance EmbPrj JS.MemberId where
  icode (JS.MemberId l) = icode l
  value n = JS.MemberId `fmap` value n

instance EmbPrj Polarity where
  icode Covariant     = icode0'
  icode Contravariant = icode0 1
  icode Invariant     = icode0 2
  icode Nonvariant    = icode0 3

  value = vcase valu where
    valu []  = valu0 Covariant
    valu [1] = valu0 Contravariant
    valu [2] = valu0 Invariant
    valu [3] = valu0 Nonvariant
    valu _   = malformed

instance EmbPrj Occurrence where
  icode StrictPos = icode0'
  icode Mixed     = icode0 1
  icode Unused    = icode0 2
  icode GuardPos  = icode0 3
  icode JustPos   = icode0 4
  icode JustNeg   = icode0 5

  value = vcase valu where
    valu []  = valu0 StrictPos
    valu [1] = valu0 Mixed
    valu [2] = valu0 Unused
    valu [3] = valu0 GuardPos
    valu [4] = valu0 JustPos
    valu [5] = valu0 JustNeg
    valu _   = malformed

instance EmbPrj CompiledRepresentation where
  icode (CompiledRep a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 CompiledRep a b c
                           valu _         = malformed

instance EmbPrj Defn where
  icode Axiom                                   = icode0 0
  icode (Function    a b c d e f g h i j)       = icode10 1 a b c d e f g h i j
  icode (Datatype    a b c d e f g h)           = icode8 2 a b c d e f g h
  icode (Record      a b c d e f g h i j k l)   = icode12 3 a b c d e f g h i j k l
  icode (Constructor a b c d e)                 = icode5 4 a b c d e
  icode (Primitive   a b c d)                   = icode4 5 a b c d
  value = vcase valu where
    valu [0]                                    = valu0 Axiom
    valu [1, a, b, c, d, e, f, g, h, i, j]      = valu10 Function a b c d e f g h i j
    valu [2, a, b, c, d, e, f, g, h]            = valu8 Datatype a b c d e f g h
    valu [3, a, b, c, d, e, f, g, h, i, j, k, l]= valu12 Record  a b c d e f g h i j k l
    valu [4, a, b, c, d, e]                     = valu5 Constructor a b c d e
    valu [5, a, b, c, d]                        = valu4 Primitive   a b c d
    valu _                                      = malformed

instance EmbPrj a => EmbPrj (WithArity a) where
  icode (WithArity a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 WithArity a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Case a) where
  icode (Branches a b c) = icode3' a b c

  value = vcase valu where
    valu [a, b, c] = valu3 Branches a b c
    valu _         = malformed

instance EmbPrj CompiledClauses where
  icode Fail       = icode0'
  icode (Done a b) = icode2' a (P.killRange b)
  icode (Case a b) = icode2 2 a b

  value = vcase valu where
    valu []        = valu0 Fail
    valu [a, b]    = valu2 Done a b
    valu [2, a, b] = valu2 Case a b
    valu _         = malformed

instance EmbPrj FunctionInverse where
  icode NotInjective = icode0'
  icode (Inverse a)  = icode1' a
  value = vcase valu where valu []  = valu0 NotInjective
                           valu [a] = valu1 Inverse a
                           valu _   = malformed

instance EmbPrj TermHead where
  icode SortHead    = icode0'
  icode PiHead      = icode0 1
  icode (ConHead a) = icode1 2 a
  value = vcase valu where valu []     = valu0 SortHead
                           valu [1]    = valu0 PiHead
                           valu [2, a] = valu1 ConHead a
                           valu _      = malformed

instance EmbPrj Agda.Syntax.Common.IsAbstract where
  icode AbstractDef = icode0 0
  icode ConcreteDef = icode0'
  value = vcase valu where valu [0] = valu0 AbstractDef
                           valu []  = valu0 ConcreteDef
                           valu _   = malformed

instance EmbPrj I.Clause where
  icode (Clause a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Clause a b c d e
                           valu _               = malformed

instance EmbPrj I.ClauseBody where
  icode (Body   a) = icode1 0 a
  icode (Bind   a) = icode1' a
  icode NoBody     = icode0'
  value = vcase valu where valu [0, a] = valu1 Body   a
                           valu [a]    = valu1 Bind   a
                           valu []     = valu0 NoBody
                           valu _      = malformed

instance EmbPrj Delayed where
  icode Delayed    = icode0 0
  icode NotDelayed = icode0'
  value = vcase valu where valu [0] = valu0 Delayed
                           valu []  = valu0 NotDelayed
                           valu _   = malformed

instance EmbPrj I.Pattern where
  icode (VarP a    ) = icode1' a
  icode (ConP a b c) = icode3' a b c
  icode (LitP a    ) = icode1 2 a
  icode (DotP a    ) = icode1 3 a
  icode (ProjP a   ) = icode1 4 a
  value = vcase valu where valu [a]       = valu1 VarP a
                           valu [a, b, c] = valu3 ConP a b c
                           valu [2, a]    = valu1 LitP a
                           valu [3, a]    = valu1 DotP a
                           valu [4, a]    = valu1 ProjP a
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icode (Prim    a) = icode1' a
  icode (Builtin a) = icode1 1 a
  value = vcase valu where valu [a]    = valu1 Prim    a
                           valu [1, a] = valu1 Builtin a
                           valu _      = malformed

instance EmbPrj HP.NameKind where
  icode HP.Bound           = icode0'
  icode (HP.Constructor a) = icode1 1 a
  icode HP.Datatype        = icode0 2
  icode HP.Field           = icode0 3
  icode HP.Function        = icode0 4
  icode HP.Module          = icode0 5
  icode HP.Postulate       = icode0 6
  icode HP.Primitive       = icode0 7
  icode HP.Record          = icode0 8

  value = vcase valu where
    valu []      = valu0 HP.Bound
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
  icode HP.Symbol        = icode0'
  icode HP.PrimitiveType = icode0 5
  icode (HP.Name mk b)   = icode2 6 mk b

  value = vcase valu where
    valu [0]        = valu0 HP.Comment
    valu [1]        = valu0 HP.Keyword
    valu [2]        = valu0 HP.String
    valu [3]        = valu0 HP.Number
    valu []         = valu0 HP.Symbol
    valu [5]        = valu0 HP.PrimitiveType
    valu [6, mk, b] = valu2 HP.Name mk b
    valu _          = malformed

instance EmbPrj HP.OtherAspect where
  icode HP.Error              = icode0 0
  icode HP.DottedPattern      = icode0'
  icode HP.UnsolvedMeta       = icode0 2
  icode HP.TerminationProblem = icode0 3
  icode HP.IncompletePattern  = icode0 4
  icode HP.TypeChecks         = icode0 5
  icode HP.UnsolvedConstraint = icode0 6

  value = vcase valu where
    valu [0] = valu0 HP.Error
    valu []  = valu0 HP.DottedPattern
    valu [2] = valu0 HP.UnsolvedMeta
    valu [3] = valu0 HP.TerminationProblem
    valu [4] = valu0 HP.IncompletePattern
    valu [5] = valu0 HP.TypeChecks
    valu [6] = valu0 HP.UnsolvedConstraint
    valu _   = malformed

instance EmbPrj HP.MetaInfo where
  icode (HP.MetaInfo a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 HP.MetaInfo a b c d
    valu _            = malformed

instance EmbPrj Precedence where
  icode TopCtx                 = icode0'
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
  icode (ScopeInfo a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 ScopeInfo a b c d
                           valu _            = malformed

instance EmbPrj HP.CompressedFile where
  icode (HP.CompressedFile f) = icode1' f
  value = vcase valu
    where
    valu [f] = valu1 HP.CompressedFile f
    valu _   = malformed

instance EmbPrj Interface where
  icode (Interface a b c d e f g h i j) = icode10' a b c d e f g h i j
  value = vcase valu
    where
      valu [a, b, c, d, e, f, g, h, i, j] = valu10 Interface a b c d e f g h i j
      valu _                              = malformed

-- This is used for the Epic compiler backend
instance EmbPrj Epic.EInterface where
  icode (Epic.EInterface a b c d e f g h) = icode8' a b c d e f g h
  value = vcase valu where
    valu [a, b, c, d, e, f, g, h] = valu8 Epic.EInterface a b c d e f g h
    valu _                        = malformed

instance EmbPrj Epic.InjectiveFun where
  icode (Epic.InjectiveFun a b) = icode2' a b
  value = vcase valu where
     valu [a,b] = valu2 Epic.InjectiveFun a b
     valu _     = malformed

instance EmbPrj Epic.Relevance where
  icode Epic.Irr      = icode0 0
  icode Epic.Rel      = icode0 1
  value = vcase valu where valu [0] = valu0 Epic.Irr
                           valu [1] = valu0 Epic.Rel
                           valu _   = malformed

instance EmbPrj Epic.Forced where
  icode Epic.Forced    = icode0 0
  icode Epic.NotForced = icode0 1
  value = vcase valu where valu [0] = valu0 Epic.Forced
                           valu [1] = valu0 Epic.NotForced
                           valu _   = malformed

instance EmbPrj Epic.Tag where
  icode (Epic.Tag a)     = icode1 0 a
  icode (Epic.PrimTag a) = icode1 1 a
  value = vcase valu
    where
    valu [0, a] = valu1 Epic.Tag a
    valu [1, a] = valu1 Epic.PrimTag a
    valu _      = malformed

icodeX :: (Eq k, Hashable k) =>
          (Dict -> HashTable k Int32) -> (Dict -> IORef Int32) ->
          k -> S Int32
icodeX dict counter key = do
  d <- asks dict
  c <- asks counter
  liftIO $ do
  mi    <- H.lookup d key
  case mi of
    Just i  -> return i
    Nothing -> do
      fresh <- readIORef c
      H.insert d key fresh
      writeIORef c $! fresh + 1
      return fresh

icodeN :: [Int32] -> S Int32
icodeN = icodeX nodeD nodeC

{-# INLINE vcase #-}
vcase :: forall a . EmbPrj a => (Node -> R a) -> Int32 -> R a
vcase valu = \ix -> do
    memo <- gets nodeMemo
    (aTyp, maybeU) <- liftIO $ do
      let aTyp = typeOf (undefined :: a)
      maybeU <- H.lookup memo (ix, aTyp)
      return (aTyp, maybeU)
    case maybeU of
      Just (U u) -> maybe malformed return (cast u)
      Nothing    -> do
          v <- valu . (! ix) =<< gets nodeE
          liftIO $ H.insert memo (ix, aTyp) (U v)
          return v

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

-- | Creates an empty dictionary.

emptyDict :: SourceToModule
             -- ^ Maps file names to the corresponding module names.
             -- Must contain a mapping for every file name that is
             -- later encountered.
          -> IO Dict
emptyDict fileMod = Dict
  <$> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef 0
  <*> newIORef (0, 0)
  <*> return fileMod
