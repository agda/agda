{-# LANGUAGE OverlappingInstances,
             GeneralizedNewtypeDeriving #-}

-- | Serialisation of Agda interface files.

-- TODO: It should be easy to produce a decent QuickCheck test suite
-- for this file.

module TypeChecking.Serialise
  ( Binary
  , encode
  , encodeFile
  , decode
  , decodeFile
  , tests
  ) where

import Control.Monad
import Control.Monad.State (StateT, MonadState)
import qualified Control.Monad.State as S
import Control.Monad.Reader (ReaderT, MonadReader)
import qualified Control.Monad.Reader as R
import Control.Monad.Trans (MonadTrans, lift)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Binary as B
import qualified Data.Binary.Put as B
import qualified Data.Binary.Get as B
import qualified Data.Binary.Builder as B
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Base as BB
import Data.Word

import Syntax.Common
import Syntax.Concrete.Name as C
import Syntax.Abstract.Name as A
import Syntax.Internal
import Syntax.Scope.Base
import Syntax.Position (Position(..), Range)
import qualified Syntax.Position as P
import Syntax.Common
import Syntax.Fixity
import Syntax.Literal

import TypeChecking.Monad

import Utils.Serialise
import Utils.Tuple

-- | Current version of the interface. Only interface files of this version
--   will be parsed.
currentInterfaceVersion :: Int
currentInterfaceVersion = 123

------------------------------------------------------------------------
-- A wrapper around Data.Binary
------------------------------------------------------------------------

-- Used to save space by replacing strings and other things with
-- unique identifiers and storing the syntax tree together with a map
-- from identifiers to such things.

-- | Things hashed by the map.

data Thing = String String
           | Range  Range
  deriving (Show, Eq, Ord)

-- | Unique identifiers.

type Id = Int

-- | Error message used below.

corruptError :: Monad m => m a
corruptError = fail "Corrupt interface file."

------------------------------------------------------------------------
-- Put

-- | State used by the 'put' instance for strings.

data PutState = PutState { thingMap      :: Map Thing Id
                           -- ^ TODO: It seems wise to use a trie
                           -- instead of a map here, at least for the
                           -- strings.
                         , lowestFreshId :: Id
                         }
  deriving Show

-- | Initial 'PutState'.

initialState :: PutState
initialState = PutState { thingMap      = Map.empty
                        , lowestFreshId = 0
                        }

-- | Looks up the string. If it doesn't already have a unique id
-- associated with it, such an association is created.

lookupId :: (Monad m, MonadState PutState m) => Thing -> m Id
lookupId th = do
  st <- S.get
  case Map.lookup th (thingMap st) of
    Nothing -> do
      let n = lowestFreshId st
      S.put (st { thingMap      = Map.insert th n (thingMap st)
                , lowestFreshId = n + 1
                })
      return n
    Just n -> return n

-- | The 'PutT' monad transformer.

newtype PutT m a = PutM { unPutT :: StateT PutState m a }
  deriving (Monad, MonadState PutState, MonadTrans)

-- | @'Put' = 'PutT' 'B.PutM' ()@.

type Put = PutT B.PutM ()

-- | Runs the put computation, producing a string plus a 'GetState'
-- mapping unique identifiers to strings.

runPut :: Put -> (L.ByteString, GetState)
runPut p = (B.toLazyByteString builder, getState)
  where
  ((_, st), builder) = B.unPut (S.runStateT (unPutT p) initialState)
  getState = IntMap.fromList $ map swap $ Map.toList $ thingMap st

  swap (x, y) = (y, x)

-- | A lifted version of 'B.putWord8'.

putWord8 :: Word8 -> Put
putWord8 w = lift (B.putWord8 w)

------------------------------------------------------------------------
-- Get

-- | A map from unique identifiers to things.

type GetState = IntMap Thing

-- | Looks up the identifier. Uses 'fail' to report missing
-- identifiers.

lookupThing :: (Monad m, MonadReader GetState m) => Id -> m Thing
lookupThing n = do
  map <- R.ask
  case IntMap.lookup n map of
    Nothing -> corruptError
    Just th -> return th

-- | The 'GetT' monad transformer.

newtype GetT m a = Get { unGetT :: ReaderT GetState m a }
  deriving (Monad, MonadReader GetState, MonadTrans)

-- | @'Get' = 'GetT' 'B.Get'@.

type Get = GetT B.Get

-- | Runs the get computation on the given string, using the given
-- 'GetState'.

runGet :: GetState -> Get a -> L.ByteString -> a
runGet st m s = B.runGet (R.runReaderT (unGetT m) st) s

-- | A lifted version of 'B.getWord8'.

getWord8 :: Get Word8
getWord8 = lift B.getWord8

------------------------------------------------------------------------
-- Binary wrapper

-- | A wrapper around 'B.Binary'.

class Binary a where
  put :: a -> Put
  get :: Get a

-- | Lifting of 'B.put'.

liftedPut :: B.Binary a => a -> Put
liftedPut = lift . B.put

-- | Lifting of 'B.get'.

liftedGet :: B.Binary a => Get a
liftedGet = lift B.get

-- | String instance (replaces strings with unique identifiers).

instance Binary String where
  put w = put =<< lookupId (String w)
  get   = do
    x <- lookupThing =<< get
    case x of
      String s -> return s
      _        -> corruptError

-- | Range instance (replaces ranges with unique identifiers).

instance Binary Range where
  put r = put =<< lookupId (Range r)
  get   = do
    x <- lookupThing =<< get
    case x of
      Range r -> return r
      _       -> corruptError

-- | Encodes the input, ensuring that strings are stored as unique
-- identifiers.
--
-- Note that the interface version is stored as the first thing in the
-- resulting string, to ensure that we can always check it; 'decode'
-- takes care of this, and fails if the version does not match.

encode :: Binary a => a -> L.ByteString
encode x = header `append` s
  where
  (s, getState) = runPut (put x)
  header        = B.encode currentInterfaceVersion `append`
                  B.encode getState

  -- L.append is currently (GHC 6.6.1) strict in its second argument,
  -- and this somehow changes the semantics of encode when this module
  -- is compiled with optimisations turned on...
  append (BB.LPS xs) (BB.LPS ys) = BB.LPS (xs ++ ys)

-- | Encodes a file, ensuring that strings are stored as unique
-- identifiers. See 'encode'.

encodeFile :: Binary a => FilePath -> a -> IO ()
encodeFile f x = L.writeFile f (encode x)

-- | Decodes something encoded by 'encode'. Fails with 'error' if the
-- interface version does not match the current interface version.

decode :: Binary a => L.ByteString -> a
decode s
  | v /= currentInterfaceVersion = error "Wrong interface version"
  | otherwise                    = runGet getState get s''
  where
  (v,        s',  _) = B.runGetState B.get s 0
  (getState, s'', _) = B.runGetState B.get s' 0

-- | Decodes a file written by 'encodeFile'.

decodeFile :: Binary a => FilePath -> IO a
decodeFile f = liftM decode $ L.readFile f

------------------------------------------------------------------------
-- More boring instances
------------------------------------------------------------------------

instance B.Binary Thing where
  put (String s) = B.putWord8 0 >> B.put s
  put (Range r)  = B.putWord8 1 >> B.put r
  get = do
    tag <- B.getWord8
    case tag of
      0 -> liftM String B.get
      1 -> liftM Range B.get
      _ -> corruptError

instance B.Binary Range where
  put (P.Range a b) = B.put a >> B.put b
  get = liftM2 P.Range B.get B.get

instance B.Binary Position where
    put NoPos	     = B.putWord8 0
    put (Pn f p l c) = B.putWord8 1 >> B.put f >> B.put p >> B.put l >> B.put c
    get = do
	tag_ <- B.getWord8
	case tag_ of
	    0	-> return NoPos
	    1	-> liftM4 Pn B.get B.get B.get B.get
	    _ -> fail "no parse"

instance Binary Double where
  put = liftedPut
  get = liftedGet

instance Binary Integer where
  put = liftedPut
  get = liftedGet

instance Binary Int where
  put = liftedPut
  get = liftedGet

instance Binary Char where
  put = liftedPut
  get = liftedGet

instance (Binary a, Binary b) => Binary (a, b) where
  put (x, y) = put x >> put y
  get = liftM2 (,) get get

instance Binary a => Binary (Maybe a) where
  put Nothing  = putWord8 0
  put (Just x) = putWord8 1 >> put x
  get = do
    tag <- getWord8
    case tag of
      0 -> return Nothing
      1 -> liftM Just get
      _ -> corruptError

instance Binary a => Binary [a] where
  put []       = putWord8 0
  put (x : xs) = putWord8 1 >> put x >> put xs
  get = do
    tag <- getWord8
    case tag of
      0 -> return []
      1 -> liftM2 (:) get get
      _ -> corruptError

instance (Eq a, Binary a, Binary b) => Binary (Map a b) where
  put = put . Map.toAscList
  get = liftM Map.fromAscList get

instance Binary C.Name where
    put (C.NoName a b) = putWord8 0 >> put a >> put b
    put (C.Name r xs) = putWord8 1 >> put r >> put xs
    get = do
      tag_ <- getWord8
      case tag_ of
	0 -> liftM2 C.NoName get get
	1 -> liftM2 C.Name get get
	_ -> fail "no parse"

instance Binary NamePart where
  put Hole     = putWord8 0
  put (Id r a) = putWord8 1 >> put r >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return Hole
      1 -> liftM2 Id get get
      _ -> fail "no parse"

instance Binary C.QName where
  put (Qual a b) = putWord8 0 >> put a >> put b
  put (C.QName a) = putWord8 1 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (Qual a b)
      1 -> get >>= \a -> return (C.QName a)
      _ -> fail "no parse"

instance Binary Scope where
  put (Scope a b c) = put a >> put b >> put c
  get = get >>= \a -> get >>= \b -> get >>= \c -> return (Scope a b c)

instance Binary Access where
  put PrivateAccess = putWord8 0
  put PublicAccess = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return PrivateAccess
      1 -> return PublicAccess
      _ -> fail "no parse"

instance Binary NameSpace where
  put (NameSpace a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (NameSpace a b)

instance Binary AbstractName where
  put (AbsName a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (AbsName a b)

instance Binary AbstractModule where
  put (AbsModule a) = put a
  get = get >>= \a -> return (AbsModule a)

instance Binary KindOfName where
  put DefName = putWord8 0
  put ConName = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return DefName
      1 -> return ConName
      _ -> fail "no parse"

instance Binary Syntax.Fixity.Fixity where
  put (LeftAssoc a b) = putWord8 0 >> put a >> put b
  put (RightAssoc a b) = putWord8 1 >> put a >> put b
  put (NonAssoc a b) = putWord8 2 >> put a >> put b
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (LeftAssoc a b)
      1 -> get >>= \a -> get >>= \b -> return (RightAssoc a b)
      2 -> get >>= \a -> get >>= \b -> return (NonAssoc a b)
      _ -> fail "no parse"

instance Binary A.QName where
  put (A.QName a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (A.QName a b)

instance Binary A.ModuleName where
  put (A.MName a) = put a
  get = get >>= \a -> return (A.MName a)

instance Binary A.Name where
  put (A.Name a b c d) = put a >> put b >> put c >> put d
  get = get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> return (A.Name a b c d)

instance Binary NameId where
  put (NameId a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (NameId a b)

instance Binary Signature where
  put (Sig a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Sig a b)

instance Binary Section where
  put (Section a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Section a b)

instance Binary Telescope where
  put EmptyTel = putWord8 0
  put (ExtendTel a b) = putWord8 1 >> put a >> put b
  get = do
    tag_ <- getWord8
    case tag_ of
      0	-> return EmptyTel
      1 -> get >>= \a -> get >>= \b -> return (ExtendTel a b)
      _ -> fail "no parse"

instance (Binary a) => Binary (Syntax.Common.Arg a) where
  put (Arg a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Arg a b)

instance Binary Syntax.Common.Hiding where
  put Hidden = putWord8 0
  put NotHidden = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return Hidden
      1 -> return NotHidden
      _ -> fail "no parse"

instance Binary Syntax.Internal.Type where
  put (El a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (El a b)

instance Binary Syntax.Internal.MetaId where
  put (MetaId a) = put a
  get = get >>= \a -> return (MetaId a)

instance (Binary a) => Binary (Syntax.Internal.Blocked a) where
  put (Blocked a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Blocked a b)

instance (Binary a) => Binary (Syntax.Internal.Abs a) where
  put (Abs a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Abs a b)

instance Binary Syntax.Internal.Term where
  put (Var a b) = putWord8 0 >> put a >> put b
  put (Lam a b) = putWord8 1 >> put a >> put b
  put (Lit a) = putWord8 2 >> put a
  put (Def a b) = putWord8 3 >> put a >> put b
  put (Con a b) = putWord8 4 >> put a >> put b
  put (Pi a b) = putWord8 5 >> put a >> put b
  put (Fun a b) = putWord8 6 >> put a >> put b
  put (Sort a) = putWord8 7 >> put a
  put (MetaV a b) = putWord8 8 >> put a >> put b
  put (BlockedV a) = putWord8 9 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (Var a b)
      1 -> get >>= \a -> get >>= \b -> return (Lam a b)
      2 -> get >>= \a -> return (Lit a)
      3 -> get >>= \a -> get >>= \b -> return (Def a b)
      4 -> get >>= \a -> get >>= \b -> return (Con a b)
      5 -> get >>= \a -> get >>= \b -> return (Pi a b)
      6 -> get >>= \a -> get >>= \b -> return (Fun a b)
      7 -> get >>= \a -> return (Sort a)
      8 -> get >>= \a -> get >>= \b -> return (MetaV a b)
      9 -> get >>= \a -> return (BlockedV a)
      _ -> fail "no parse"

instance Binary Syntax.Internal.Sort where
  put (Type a) = putWord8 0 >> put a
  put Prop = putWord8 1
  put (Lub a b) = putWord8 2 >> put a >> put b
  put (Suc a) = putWord8 3 >> put a
  put (MetaS a) = putWord8 4 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> return (Type a)
      1 -> return Prop
      2 -> get >>= \a -> get >>= \b -> return (Lub a b)
      3 -> get >>= \a -> return (Suc a)
      4 -> get >>= \a -> return (MetaS a)
      _ -> fail "no parse"

instance Binary Syntax.Literal.Literal where
  put (LitInt a b) = putWord8 0 >> put a >> put b
  put (LitFloat a b) = putWord8 1 >> put a >> put b
  put (LitString a b) = putWord8 2 >> put a >> put b
  put (LitChar a b) = putWord8 3 >> put a >> put b
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> get >>= \b -> return (LitInt a b)
      1 -> get >>= \a -> get >>= \b -> return (LitFloat a b)
      2 -> get >>= \a -> get >>= \b -> return (LitString a b)
      3 -> get >>= \a -> get >>= \b -> return (LitChar a b)
      _ -> fail "no parse"

instance Binary DisplayForm where
  put NoDisplay = putWord8 0
  put (Display a b c) = putWord8 1 >> put a >> put b >> put c
  get = do
    tag_ <- getWord8
    case tag_ of
      0	-> return NoDisplay
      1 -> get >>= \a -> get >>= \b -> get >>= \c -> return (Display a b c)
      _ -> fail "no parse"

instance Binary DisplayTerm where
  put (DTerm a) = putWord8 0 >> put a
  put (DWithApp a b) = putWord8 1 >> put a >> put b
  get = do
    tag_ <- getWord8
    case tag_ of
      0	-> get >>= \a -> return (DTerm a)
      1 -> get >>= \a -> get >>= \b -> return (DWithApp a b)
      _	-> fail "no parse"

instance Binary Definition where
  put (Defn a b c d) = put a >> put b >> put c >> put d
  get = get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> return (Defn a b c d)

instance Binary Defn where
  put Axiom		     = putWord8 0
  put (Function a b)	     = putWord8 1 >> put a >> put b
  put (Datatype a b c d e f) = putWord8 2 >> put a >> put b >> put c >> put d >> put e >> put f
  put (Record a b c d e f)   = putWord8 3 >> put a >> put b >> put c >> put d >> put e >> put f
  put (Constructor a b c d)  = putWord8 4 >> put a >> put b >> put c >> put d
  put (Primitive a b c)	     = putWord8 5 >> put a >> put b >> put c
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return Axiom
      1 -> get >>= \a -> get >>= \b -> return (Function a b)
      2 -> get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> get >>= \e -> get >>= \f -> return (Datatype a b c d e f)
      3 -> get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> get >>= \e -> get >>= \f -> return (Record a b c d e f)
      4 -> get >>= \a -> get >>= \b -> get >>= \c -> get >>= \d -> return (Constructor a b c d)
      5 -> get >>= \a -> get >>= \b -> get >>= \c -> return (Primitive a b c)
      _ -> fail "no parse"

instance Binary Syntax.Common.IsAbstract where
  put AbstractDef = putWord8 0
  put ConcreteDef = putWord8 1
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> return AbstractDef
      1 -> return ConcreteDef
      _ -> fail "no parse"

instance Binary Syntax.Internal.Clause where
  put (Clause a b) = put a >> put b
  get = get >>= \a -> get >>= \b -> return (Clause a b)

instance Binary Syntax.Internal.ClauseBody where
  put (Body a) = putWord8 0 >> put a
  put (Bind a) = putWord8 1 >> put a
  put (NoBind a) = putWord8 2 >> put a
  put NoBody = putWord8 3
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> return (Body a)
      1 -> get >>= \a -> return (Bind a)
      2 -> get >>= \a -> return (NoBind a)
      3 -> return NoBody
      _ -> fail "no parse"

instance Binary Syntax.Internal.Pattern where
  put (VarP a) = putWord8 0 >> put a
  put (ConP a b) = putWord8 1 >> put a >> put b
  put (LitP a) = putWord8 2 >> put a
  get = do
    tag_ <- getWord8
    case tag_ of
      0 -> get >>= \a -> return (VarP a)
      1 -> get >>= \a -> get >>= \b -> return (ConP a b)
      2 -> get >>= \a -> return (LitP a)
      _ -> fail "no parse"

instance Binary a => Binary (Builtin a) where
    put (Prim a) = putWord8 0 >> put a
    put (Builtin a) = putWord8 1 >> put a
    get = do
	tag_ <- getWord8
	case tag_ of
	    0	-> liftM Prim get
	    1	-> liftM Builtin get
	    _ -> fail "no parse"

instance Binary Interface where
    put (Interface a b c d e) = put a >> put b >> put c >> put d >> put e
    get = liftM5 Interface get get get get get

------------------------------------------------------------------------
-- All tests
------------------------------------------------------------------------

tests = do
  print (test strings)
  mapM_ (print . test) strings

  where
  test x = decode (encode x) == x

  strings = ["apa", "bepa", "∀ ∃"]
