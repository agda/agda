{-# LANGUAGE OverlappingInstances,
             TypeSynonymInstances,
             DeriveDataTypeable,
             CPP #-}
{-# OPTIONS_GHC -O6 #-}

-- | Structure-sharing serialisation of Agda interface files.

-- TODO: It should be easy to produce a decent QuickCheck test suite
-- for this file.

module Agda.TypeChecking.SerialiseShare
  ( encode
  , encodeFile
  , decode
  , decodeFile
  )
  where

import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Array.IArray
import Data.ByteString.Lazy as L
import Data.Char (ord, chr)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.List as List
import qualified Codec.Compression.GZip as G

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position (Position(..), Range)
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import qualified Agda.Utils.IO
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Utils.Function (on)

currentInterfaceVersion :: Int
currentInterfaceVersion = 20080530

type Node = [Int] -- constructor tag (maybe omitted) and arg indices

data Dict = Dict{ nodeD     :: !(Map Node    Int)
                , stringD   :: !(Map String  Int)
                , integerD  :: !(Map Integer Int)
                , doubleD   :: !(Map Double  Int)
                }
          deriving (Eq, Ord, Show)

data Env  = Env { nodeE     :: !(Array Int Node)
                , stringE   :: !(Array Int String)
                , integerE  :: !(Array Int Integer)
                , doubleE   :: !(Array Int Double)
                }
          deriving (Eq, Ord, Show)

type S a = State  Dict a
type R a = Reader Env  a

class EmbPrj a where
  icode :: a -> S Int
  value :: Int -> R a

encode :: EmbPrj a => a -> ByteString
encode a = let (root, Dict nD sD iD dD) = runState (icode a) emptyDict in
           B.encode currentInterfaceVersion `L.append`
           G.compress (B.encode (root, l nD, l sD, l iD, l dD))
  where l = List.map fst . List.sortBy (compare `on` snd) . M.toList

decode :: EmbPrj a => ByteString -> a
decode s | ver /= currentInterfaceVersion = error "Wrong interface version"
         | otherwise                      = runReader (value r) env
  where (ver                , s1, _) = B.runGetState B.get s                 0
        ((r, nL, sL, iL, dL), s2, _) = B.runGetState B.get (G.decompress s1) 0
        env  = Env (ar nL) (ar sL) (ar iL) (ar dL)
        ar l = listArray (0, List.length l - 1) l

encodeFile :: EmbPrj a => FilePath -> a -> IO ()
encodeFile f x = L.writeFile f (encode x)

decodeFile :: EmbPrj a => FilePath -> IO a
decodeFile f = liftM decode $ L.readFile f


instance EmbPrj String where
  icode s = icodeX stringD  (\d st -> st{stringD  = d}) s
  value i = (! i) `fmap` asks stringE

instance EmbPrj Integer where
  icode i = icodeX integerD (\d st -> st{integerD = d}) i
  value i = (! i) `fmap` asks integerE

instance EmbPrj Int where
  icode i = return i
  value i = return i

instance EmbPrj Char where
  icode c = return (ord c)
  value i = return (chr i)

instance EmbPrj Double where
  icode x = icodeX doubleD (\d st -> st{doubleD = d}) x
  value i = (! i) `fmap` asks doubleE

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icode (a, b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 (,) a b
                           valu _      = corrupt "(,)"

instance EmbPrj a => EmbPrj (Maybe a) where
  icode Nothing  = icode0'
  icode (Just x) = icode1' x
  value = vcase valu where valu []  = valu0 Nothing
                           valu [x] = valu1 Just x
                           valu _   = corrupt "Maybe"

instance EmbPrj Position where
  icode (P.Pn file pos line col) = icode4' file pos line col
  icode (P.NoPos               ) = icode0'
  value = vcase valu where valu [f, p, l, c] = valu4 P.Pn f p l c
                           valu []           = valu0 P.NoPos
                           valu _            = corrupt "Position"

instance EmbPrj a => EmbPrj [a] where
  icode xs = icodeN =<< mapM icode xs
  value = vcase $ mapM value
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = corrupt "List"

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icode m = icode (M.toList m)
  value m = M.fromList `fmap` value m

instance EmbPrj Range where
  icode (P.Range p q) = icode2' p q
  value = vcase valu where valu [p, q] = valu2 P.Range p q
                           valu _      = corrupt "Range"

instance EmbPrj C.Name where
  icode (C.NoName a b) = icode2 0 a b
  icode (C.Name r xs ) = icode2 1 r xs
  value = vcase valu where valu [0, a, b ] = valu2 C.NoName a b
                           valu [1, r, xs] = valu2 C.Name   r xs
                           valu _          = corrupt "C.Name"

instance EmbPrj NamePart where
  icode Hole     = icode0'
  icode (Id r a) = icode2' r a
  value = vcase valu where valu []     = valu0 Hole
                           valu [r, a] = valu2 Id r a
                           valu _      = corrupt "NamePart"

instance EmbPrj C.QName where
  icode (Qual    a b) = icode2' a b
  icode (C.QName a  ) = icode1' a
  value = vcase valu where valu [a, b] = valu2 Qual    a b
                           valu [a]    = valu1 C.QName a
                           valu _      = corrupt "C.QName"

instance EmbPrj Scope where
  icode (Scope a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Scope a b c
                           valu _         = corrupt "Scope"

instance EmbPrj Access where
  icode PrivateAccess = icode0 0
  icode PublicAccess  = icode0 1
  value = vcase valu where valu [0] = valu0 PrivateAccess
                           valu [1] = valu0 PublicAccess
                           valu _   = corrupt "Access"

instance EmbPrj NameSpace where
  icode (NameSpace a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameSpace a b
                           valu _      = corrupt "NameSpace"

instance EmbPrj AbstractName where
  icode (AbsName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 AbsName a b
                           valu _      = corrupt "AbstractName"

instance EmbPrj AbstractModule where
  icode (AbsModule a) = icode a
  value n = AbsModule `fmap` value n

instance EmbPrj KindOfName where
  icode DefName = icode0 0
  icode ConName = icode0 1
  value = vcase valu where valu [0] = valu0 DefName
                           valu [1] = valu0 ConName
                           valu _   = corrupt "KindOfName"

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icode (LeftAssoc  a b) = icode2 0 a b
  icode (RightAssoc a b) = icode2 1 a b
  icode (NonAssoc   a b) = icode2 2 a b
  value = vcase valu where valu [0, a, b] = valu2 LeftAssoc  a b
                           valu [1, a, b] = valu2 RightAssoc a b
                           valu [2, a, b] = valu2 NonAssoc   a b
                           valu _         = corrupt "Agda.Syntax.Fixity.Fixity"

instance EmbPrj A.QName where
  icode (A.QName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 A.QName a b
                           valu _      = corrupt "A.QName"

instance EmbPrj A.ModuleName where
  icode (A.MName a) = icode a
  value n = A.MName `fmap` value n

instance EmbPrj A.Name where
  icode (A.Name a b c d) = icode4' a b c d 
  value = vcase valu where valu [a, b, c, d] = valu4 A.Name a b c d
                           valu _            = corrupt "A.Name"

instance EmbPrj NameId where
  icode (NameId a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameId a b
                           valu _      = corrupt "NameId"

instance EmbPrj Signature where
  icode (Sig a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Sig a b
                           valu _      = corrupt "Signature"

instance EmbPrj Section where
  icode (Section a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Section a b
                           valu _      = corrupt "Section"

instance EmbPrj Telescope where
  icode EmptyTel        = icode0'
  icode (ExtendTel a b) = icode2' a b
  value = vcase valu where valu []     = valu0 EmptyTel
                           valu [a, b] = valu2 ExtendTel a b
                           valu _      = corrupt "Telescope"

instance EmbPrj Permutation where
  icode (Perm a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Perm a b
                           valu _      = corrupt "Permutation"

instance (EmbPrj a) => EmbPrj (Agda.Syntax.Common.Arg a) where
  icode (Arg a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Arg a b
                           valu _      = corrupt "Agda.Syntax.Common.Arg"
  
instance EmbPrj Agda.Syntax.Common.Hiding where
  icode Hidden    = icode0 0
  icode NotHidden = icode0 1
  value = vcase valu where valu [0] = valu0 Hidden
                           valu [1] = valu0 NotHidden
                           valu _   = corrupt "Agda.Syntax.Common.Hiding"

instance EmbPrj Agda.Syntax.Internal.Type where
  icode (El a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 El a b
                           valu _      = corrupt "Agda.Syntax.Internal.Type"

instance EmbPrj Agda.Syntax.Internal.MetaId where
  icode (MetaId a) = icode a
  value n = MetaId `fmap` value n

instance (EmbPrj a) => EmbPrj (Agda.Syntax.Internal.Blocked a) where
  icode (Blocked a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Blocked a b
                           valu _      = corrupt "Agda.Syntax.Internal.Blocked"

instance (EmbPrj a) => EmbPrj (Agda.Syntax.Internal.Abs a) where
  icode (Abs a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Abs a b
                           valu _      = corrupt "Agda.Syntax.Internal.Abs"

instance EmbPrj Agda.Syntax.Internal.Term where
  icode (Var      a b) = icode2 0 a b
  icode (Lam      a b) = icode2 1 a b
  icode (Lit      a  ) = icode1 2 a
  icode (Def      a b) = icode2 3 a b
  icode (Con      a b) = icode2 4 a b
  icode (Pi       a b) = icode2 5 a b
  icode (Fun      a b) = icode2 6 a b
  icode (Sort     a  ) = icode1 7 a
  icode (MetaV    a b) = icode2 8 a b
  icode (BlockedV a  ) = icode1 9 a
  value = vcase valu where valu [0, a, b] = valu2 Var   a b 
                           valu [1, a, b] = valu2 Lam   a b 
                           valu [2, a]    = valu1 Lit   a
                           valu [3, a, b] = valu2 Def   a b
                           valu [4, a, b] = valu2 Con   a b
                           valu [5, a, b] = valu2 Pi    a b
                           valu [6, a, b] = valu2 Fun   a b
                           valu [7, a]    = valu1 Sort  a
                           valu [8, a, b] = valu2 MetaV a b
                           valu [9, a]    = valu1 BlockedV a
                           valu _         = corrupt "Agda.Syntax.Internal.Term"

instance EmbPrj Agda.Syntax.Internal.Sort where
  icode (Type  a  ) = icode1 0 a
  icode Prop        = icode0 1
  icode (Lub   a b) = icode2 2 a b
  icode (Suc   a  ) = icode1 3 a
  icode (MetaS a )  = icode1 4 a
  value = vcase valu where valu [0, a]    = valu1 Type  a
                           valu [1]       = valu0 Prop
                           valu [2, a, b] = valu2 Lub   a b
                           valu [3, a]    = valu1 Suc   a
                           valu [4, a]    = valu1 MetaS a
                           valu _         = corrupt "Agda.Syntax.Internal.Sort"

instance EmbPrj Agda.Syntax.Literal.Literal where
  icode (LitInt    a b) = icode2 0 a b
  icode (LitFloat  a b) = icode2 1 a b
  icode (LitString a b) = icode2 2 a b
  icode (LitChar   a b) = icode2 3 a b
  value = vcase valu where valu [0, a, b] = valu2 LitInt    a b
                           valu [1, a, b] = valu2 LitFloat  a b
                           valu [2, a, b] = valu2 LitString a b
                           valu [3, a, b] = valu2 LitChar   a b
                           valu _         = corrupt "Agda.Syntax.Internal.Literal"

instance EmbPrj DisplayForm where
  icode (Display a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Display a b c
                           valu _         = corrupt "DisplayForm"

instance EmbPrj a => EmbPrj (Open a) where
  icode (OpenThing a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 OpenThing a b
                           valu _      = corrupt "Open"

instance EmbPrj CtxId where
  icode (CtxId a) = icode a
  value n = CtxId `fmap` value n

instance EmbPrj DisplayTerm where
  icode (DTerm    a  ) = icode1' a
  icode (DWithApp a b) = icode2' a b
  value = vcase valu where valu [a]    = valu1 DTerm a
                           valu [a, b] = valu2 DWithApp a b
                           valu _      = corrupt "DisplayTerm"

instance EmbPrj MutualId where
  icode (MutId a) = icode a
  value n = MutId `fmap` value n

instance EmbPrj Definition where
  icode (Defn a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Defn a b c d e
                           valu _               = corrupt "Definition"

instance EmbPrj Defn where
  icode (Axiom       a)           = icode1 0 a
  icode (Function    a b c)       = icode3 1 a b c
  icode (Datatype    a b c d e f) = icode6 2 a b c d e f
  icode (Record      a b c d e f) = icode6 3 a b c d e f
  icode (Constructor a b c d e)   = icode5 4 a b c d e
  icode (Primitive   a b c)       = icode3 5 a b c
  value = vcase valu where
    valu [0, a]                = valu1 Axiom       a
    valu [1, a, b, c]          = valu3 Function    a b c
    valu [2, a, b, c, d, e, f] = valu6 Datatype    a b c d e f
    valu [3, a, b, c, d, e, f] = valu6 Record      a b c d e f
    valu [4, a, b, c, d, e]    = valu5 Constructor a b c d e
    valu [5, a, b, c]          = valu3 Primitive   a b c
    valu _                     = corrupt "Defn"

instance EmbPrj FunctionInverse where
  icode NotInjective = icode0'
  icode (Inverse a)  = icode1' a
  value = vcase valu where valu []  = valu0 NotInjective
                           valu [a] = valu1 Inverse a
                           valu _   = corrupt "FunctionInverse"

instance EmbPrj TermHead where
  icode SortHead    = icode0 0
  icode PiHead      = icode0 1
  icode (ConHead a) = icode1 2 a
  value = vcase valu where valu [0]    = return SortHead
                           valu [1]    = return PiHead
                           valu [2, a] = valu1 ConHead a
                           valu _      = corrupt "TermHead"

instance EmbPrj Agda.Syntax.Common.IsAbstract where
  icode AbstractDef = icode0 0
  icode ConcreteDef = icode0 1
  value = vcase valu where valu [0] = valu0 AbstractDef
                           valu [1] = valu0 ConcreteDef
                           valu _   = corrupt "Agda.Syntax.Common.IsAbstract"

instance EmbPrj Agda.Syntax.Internal.Clause where
  icode (Clause a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 Clause a b c d
                           valu _            = corrupt "Agda.Syntax.Internal.Clause"

instance EmbPrj Agda.Syntax.Internal.ClauseBody where
  icode (Body   a) = icode1 0 a
  icode (Bind   a) = icode1 1 a
  icode (NoBind a) = icode1 2 a
  icode NoBody     = icode0'
  value = vcase valu where valu [0, a] = valu1 Body   a
                           valu [1, a] = valu1 Bind   a
                           valu [2, a] = valu1 NoBind a
                           valu []     = valu0 NoBody
                           valu _      = corrupt "Agda.Syntax.Internal.ClauseBody"

instance EmbPrj Agda.Syntax.Internal.Pattern where
  icode (VarP a  ) = icode1 0 a
  icode (ConP a b) = icode2 1 a b
  icode (LitP a  ) = icode1 2 a
  icode (DotP a  ) = icode1 3 a
  value = vcase valu where valu [0, a]    = valu1 VarP a
                           valu [1, a, b] = valu2 ConP a b
                           valu [2, a]    = valu1 LitP a
                           valu [3, a]    = valu1 DotP a
                           valu _         = corrupt "Agda.Syntax.Internal.Pattern"

instance EmbPrj a => EmbPrj (Builtin a) where
  icode (Prim    a) = icode1 0 a
  icode (Builtin a) = icode1 1 a
  value = vcase valu where valu [0, a] = valu1 Prim    a
                           valu [1, a] = valu1 Builtin a
                           valu _      = corrupt "Builtin"

instance EmbPrj Interface where
  icode (Interface a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 Interface a b c d
                           valu _            = corrupt "Interface"



icodeX :: Ord k =>
         (Dict -> Map k Int) -> (Map k Int -> Dict -> Dict) -> k -> S Int
icodeX dict upd key = do
  d <- gets dict
  let fresh = M.size d
  case M.insertLookupWithKey (\k i j -> j) key fresh d of
    (Just i , _ ) -> return i
    (Nothing, d') -> modify (upd d') >> return fresh

icodeN = icodeX nodeD (\d st -> st{nodeD = d})

vcase valu ix =  valu . (! ix) =<< asks nodeE

icode0 tag               = icodeN [tag]
icode1 tag a             = icodeN . (tag :) =<< sequence [icode a]
icode2 tag a b           = icodeN . (tag :) =<< sequence [icode a, icode b]
icode3 tag a b c         = icodeN . (tag :) =<< sequence [icode a, icode b, icode c]
icode4 tag a b c d       = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d]
icode5 tag a b c d e     = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6 tag a b c d e f   = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7 tag a b c d e f g = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]

icode0'               = icodeN []
icode1' a             = icodeN =<< sequence [icode a]
icode2' a b           = icodeN =<< sequence [icode a, icode b]
icode3' a b c         = icodeN =<< sequence [icode a, icode b, icode c]
icode4' a b c d       = icodeN =<< sequence [icode a, icode b, icode c, icode d]
icode5' a b c d e     = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6' a b c d e f   = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7' a b c d e f g = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]

valu0 h               = return h
valu1 h a             = fmap  h                  (value a)
valu2 h a b           = valu1 h a           `ap` (value b)
valu3 h a b c         = valu2 h a b         `ap` (value c)
valu4 h a b c d       = valu3 h a b c       `ap` (value d)
valu5 h a b c d e     = valu4 h a b c d     `ap` (value e)
valu6 h a b c d e f   = valu5 h a b c d e   `ap` (value f)
valu7 h a b c d e f g = valu6 h a b c d e f `ap` (value g)

corrupt msg = error $ "Serialize: corrupt interface? (" ++ msg ++")"

test :: EmbPrj a => a -> a
test x = decode (encode x)

emptyDict = Dict M.empty M.empty M.empty M.empty
