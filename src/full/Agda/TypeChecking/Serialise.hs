{-# LANGUAGE OverlappingInstances,
             TypeSynonymInstances,
             ExistentialQuantification,
             ScopedTypeVariables,
             CPP
             #-}
{-# OPTIONS_GHC -O6 #-}

-- | Structure-sharing serialisation of Agda interface files.

-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-
-- NOTE: Every time the interface format is changed the interface
-- version number should be bumped _in the same patch_.
-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-

-- TODO: It should be easy to produce a decent QuickCheck test suite
-- for this file.

module Agda.TypeChecking.Serialise
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
import Data.Bits (shiftR)
import Data.ByteString.Lazy as L
import Data.Char (ord, chr)
import Data.HashTable (HashTable)
import qualified Data.HashTable as H
import Data.Int (Int32, Int64)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.List as List
import Data.Function
import Data.Generics
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
import Agda.Syntax.Literal
import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP

import Agda.TypeChecking.Monad
import Agda.Utils.Tuple
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible

currentInterfaceVersion :: Int
currentInterfaceVersion = 20090107

type Node = [Int] -- constructor tag (maybe omitted) and arg indices

data Dict = Dict{ nodeD     :: !(HashTable Node    Int)
                , stringD   :: !(HashTable String  Int)
                , integerD  :: !(HashTable Integer Int)
                , doubleD   :: !(HashTable Double  Int)
                , nodeC     :: !(IORef Int)  -- counters for fresh indexes
                , stringC   :: !(IORef Int)
                , integerC  :: !(IORef Int)
                , doubleC   :: !(IORef Int)
                }

data U    = forall a . Data a => U !a
type Memo = HashTable (Int, Int) U    -- (node index, type rep key)

data Env  = Env { nodeE     :: !(Array Int Node)
                , stringE   :: !(Array Int String)
                , integerE  :: !(Array Int Integer)
                , doubleE   :: !(Array Int Double)
                , nodeMemo  :: !Memo
                }

type S a = ReaderT Dict IO a
type R a = ReaderT Env  IO a

class Data a => EmbPrj a where
  icode :: a -> S Int
  value :: Int -> R a


encode :: EmbPrj a => a -> IO ByteString
encode a = do
    newD@(Dict nD sD iD dD _ _ _ _) <- emptyDict
    root <- runReaderT (icode a) newD
    nL <- l nD; sL <- l sD; iL <- l iD; dL <- l dD
    return $ B.encode currentInterfaceVersion `L.append`
             G.compress (B.encode (root, nL, sL, iL, dL))
  where l = fmap (List.map fst . List.sortBy (compare `on` snd)) . H.toList

decode :: EmbPrj a => ByteString -> IO a
decode s | ver /= currentInterfaceVersion = error "Wrong interface version"
         | otherwise = runReaderT (value r) . env =<< H.new (==) hashInt2
  where (ver                , s1, _) = B.runGetState B.get s                 0
        ((r, nL, sL, iL, dL), s2, _) = B.runGetState B.get (G.decompress s1) 0
        ar l = listArray (0, List.length l - 1) l
        env  = Env (ar nL) (ar sL) (ar iL) (ar dL)

encodeFile :: EmbPrj a => FilePath -> a -> IO ()
encodeFile f x = L.writeFile f =<< encode x

decodeFile :: EmbPrj a => FilePath -> IO a
decodeFile f = decode =<< L.readFile f


instance EmbPrj String where
  icode   = icodeX stringD stringC
  value i = (! i) `fmap` asks stringE

instance EmbPrj Integer where
  icode   = icodeX integerD integerC
  value i = (! i) `fmap` asks integerE

instance EmbPrj Int where
  icode i = return i
  value i = return i

instance EmbPrj Char where
  icode c = return (ord c)
  value i = return (chr i)

instance EmbPrj Double where
  icode   = icodeX doubleD doubleC
  value i = (! i) `fmap` asks doubleE

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icode (a, b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 (,) a b
                           valu _      = __IMPOSSIBLE__

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icode (a, b, c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 (,,) a b c
                           valu _         = __IMPOSSIBLE__

instance EmbPrj a => EmbPrj (Maybe a) where
  icode Nothing  = icode0'
  icode (Just x) = icode1' x
  value = vcase valu where valu []  = valu0 Nothing
                           valu [x] = valu1 Just x
                           valu _   = __IMPOSSIBLE__

instance EmbPrj Bool where
  icode True  = icode0 0
  icode False = icode0 1
  value = vcase valu where valu [0] = valu0 True
                           valu [1] = valu0 False
                           valu _   = __IMPOSSIBLE__

instance EmbPrj Position where
  icode (P.Pn file pos line col) = icode4' file pos line col
  value = vcase valu where valu [f, p, l, c] = valu4 P.Pn f p l c
                           valu _            = __IMPOSSIBLE__

instance EmbPrj a => EmbPrj [a] where
  icode xs = icodeN =<< mapM icode xs
  value = vcase $ mapM value
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = __IMPOSSIBLE__

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icode m = icode (M.toList m)
  value m = M.fromList `fmap` value m

instance EmbPrj P.Interval where
  icode (P.Interval p q) = icode2' p q
  value = vcase valu where valu [p, q] = valu2 P.Interval p q
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Range where
  icode (P.Range is) = icode1' is
  value = vcase valu where valu [is] = valu1 P.Range is
                           valu _    = __IMPOSSIBLE__

instance EmbPrj HR.Range where
  icode (HR.Range a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 HR.Range a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj C.Name where
  icode (C.NoName a b) = icode2 0 a b
  icode (C.Name r xs)  = icode2 1 r xs
  value = vcase valu where valu [0, a, b]  = valu2 C.NoName a b
                           valu [1, r, xs] = valu2 C.Name   r xs
                           valu _          = __IMPOSSIBLE__

instance EmbPrj NamePart where
  icode Hole   = icode0'
  icode (Id a) = icode1' a
  value = vcase valu where valu []  = valu0 Hole
                           valu [a] = valu1 Id a
                           valu _   = __IMPOSSIBLE__

instance EmbPrj C.QName where
  icode (Qual    a b) = icode2' a b
  icode (C.QName a  ) = icode1' a
  value = vcase valu where valu [a, b] = valu2 Qual    a b
                           valu [a]    = valu1 C.QName a
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Scope where
  icode (Scope a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Scope a b c
                           valu _         = __IMPOSSIBLE__

instance EmbPrj Access where
  icode PrivateAccess = icode0 0
  icode PublicAccess  = icode0 1
  value = vcase valu where valu [0] = valu0 PrivateAccess
                           valu [1] = valu0 PublicAccess
                           valu _   = __IMPOSSIBLE__

instance EmbPrj NameSpace where
  icode (NameSpace a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameSpace a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj AbstractName where
  icode (AbsName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 AbsName a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj AbstractModule where
  icode (AbsModule a) = icode a
  value n = AbsModule `fmap` value n

instance EmbPrj KindOfName where
  icode DefName = icode0 0
  icode ConName = icode0 1
  value = vcase valu where valu [0] = valu0 DefName
                           valu [1] = valu0 ConName
                           valu _   = __IMPOSSIBLE__

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icode (LeftAssoc  a b) = icode2 0 a b
  icode (RightAssoc a b) = icode2 1 a b
  icode (NonAssoc   a b) = icode2 2 a b
  value = vcase valu where valu [0, a, b] = valu2 LeftAssoc  a b
                           valu [1, a, b] = valu2 RightAssoc a b
                           valu [2, a, b] = valu2 NonAssoc   a b
                           valu _         = __IMPOSSIBLE__

instance EmbPrj A.QName where
  icode (A.QName a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 A.QName a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj A.ModuleName where
  icode (A.MName a) = icode a
  value n = A.MName `fmap` value n

instance EmbPrj A.Name where
  icode (A.Name a b c d) = icode4' a b c d 
  value = vcase valu where valu [a, b, c, d] = valu4 A.Name a b c d
                           valu _            = __IMPOSSIBLE__

instance EmbPrj NameId where
  icode (NameId a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameId a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Signature where
  icode (Sig a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Sig a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Section where
  icode (Section a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Section a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Telescope where
  icode EmptyTel        = icode0'
  icode (ExtendTel a b) = icode2' a b
  value = vcase valu where valu []     = valu0 EmptyTel
                           valu [a, b] = valu2 ExtendTel a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Permutation where
  icode (Perm a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Perm a b
                           valu _      = __IMPOSSIBLE__

instance (EmbPrj a) => EmbPrj (Agda.Syntax.Common.Arg a) where
  icode (Arg a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Arg a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Agda.Syntax.Common.Recursion where
  icode Recursive   = icode0 0
  icode CoRecursive = icode0 1
  value = vcase valu where valu [0] = valu0 Recursive
                           valu [1] = valu0 CoRecursive
                           valu _   = __IMPOSSIBLE__

instance EmbPrj Agda.Syntax.Common.Induction where
  icode Inductive   = icode0 0
  icode CoInductive = icode0 1
  value = vcase valu where valu [0] = valu0 Inductive
                           valu [1] = valu0 CoInductive
                           valu _   = __IMPOSSIBLE__

instance EmbPrj Agda.Syntax.Common.Hiding where
  icode Hidden    = icode0 0
  icode NotHidden = icode0 1
  value = vcase valu where valu [0] = valu0 Hidden
                           valu [1] = valu0 NotHidden
                           valu _   = __IMPOSSIBLE__

instance EmbPrj I.Type where
  icode (El a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 El a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj I.MetaId where
  icode (MetaId a) = icode a
  value n = MetaId `fmap` value n

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icode (Abs a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Abs a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj I.Term where
  icode (Var      a b) = icode2 0 a b
  icode (Lam      a b) = icode2 1 a b
  icode (Lit      a  ) = icode1 2 a
  icode (Def      a b) = icode2 3 a b
  icode (Con      a b) = icode2 4 a b
  icode (Pi       a b) = icode2 5 a b
  icode (Fun      a b) = icode2 6 a b
  icode (Sort     a  ) = icode1 7 a
  icode (MetaV    a b) = icode2 8 a b
  value = vcase valu where valu [0, a, b] = valu2 Var   a b 
                           valu [1, a, b] = valu2 Lam   a b 
                           valu [2, a]    = valu1 Lit   a
                           valu [3, a, b] = valu2 Def   a b
                           valu [4, a, b] = valu2 Con   a b
                           valu [5, a, b] = valu2 Pi    a b
                           valu [6, a, b] = valu2 Fun   a b
                           valu [7, a]    = valu1 Sort  a
                           valu [8, a, b] = valu2 MetaV a b
                           valu _         = __IMPOSSIBLE__

instance EmbPrj I.Sort where
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
                           valu _         = __IMPOSSIBLE__

instance EmbPrj Agda.Syntax.Literal.Literal where
  icode (LitInt    a b) = icode2 0 a b
  icode (LitFloat  a b) = icode2 1 a b
  icode (LitString a b) = icode2 2 a b
  icode (LitChar   a b) = icode2 3 a b
  value = vcase valu where valu [0, a, b] = valu2 LitInt    a b
                           valu [1, a, b] = valu2 LitFloat  a b
                           valu [2, a, b] = valu2 LitString a b
                           valu [3, a, b] = valu2 LitChar   a b
                           valu _         = __IMPOSSIBLE__

instance EmbPrj DisplayForm where
  icode (Display a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Display a b c
                           valu _         = __IMPOSSIBLE__

instance EmbPrj a => EmbPrj (Open a) where
  icode (OpenThing a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 OpenThing a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj CtxId where
  icode (CtxId a) = icode a
  value n = CtxId `fmap` value n

instance EmbPrj DisplayTerm where
  icode (DTerm    a  ) = icode1' a
  icode (DWithApp a b) = icode2' a b
  value = vcase valu where valu [a]    = valu1 DTerm a
                           valu [a, b] = valu2 DWithApp a b
                           valu _      = __IMPOSSIBLE__

instance EmbPrj MutualId where
  icode (MutId a) = icode a
  value n = MutId `fmap` value n

instance EmbPrj Definition where
  icode (Defn a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Defn a b c d e
                           valu _               = __IMPOSSIBLE__

instance EmbPrj HaskellRepresentation where
  icode (HsType a)   = icode1 0 a
  icode (HsDefn a b) = icode2 1 a b

  value = vcase valu where
    valu [0, a]    = valu1 HsType a
    valu [1, a, b] = valu2 HsDefn a b
    valu _         = __IMPOSSIBLE__

instance EmbPrj Polarity where
  icode Covariant     = icode0 0
  icode Contravariant = icode0 1
  icode Invariant     = icode0 2

  value = vcase valu where
    valu [0] = valu0 Covariant
    valu [1] = valu0 Contravariant
    valu [2] = valu0 Invariant
    valu _   = __IMPOSSIBLE__

instance EmbPrj Occurrence where
  icode Positive = icode0 0
  icode Negative = icode0 1
  icode Unused   = icode0 2

  value = vcase valu where
    valu [0] = valu0 Positive
    valu [1] = valu0 Negative
    valu [2] = valu0 Unused
    valu _   = __IMPOSSIBLE__

instance EmbPrj Defn where
  icode (Axiom       a)                   = icode1 0 a
  icode (Function    a b c d e f)         = icode6 1 a b c d e f
  icode (Datatype    a b c d e f g h i j) = icode10 2 a b c d e f g h i j
  icode (Record      a b c d e f g h)     = icode8 3 a b c d e f g h
  icode (Constructor a b c d e f)         = icode6 4 a b c d e f
  icode (Primitive   a b c)               = icode3 5 a b c
  value = vcase valu where
    valu [0, a]                            = valu1 Axiom       a
    valu [1, a, b, c, d, e, f]             = valu6 Function    a b c d e f
    valu [2, a, b, c, d, e, f, g, h, i, j] = valu10 Datatype    a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h]       = valu8 Record      a b c d e f g h
    valu [4, a, b, c, d, e, f]             = valu6 Constructor a b c d e f
    valu [5, a, b, c]                      = valu3 Primitive   a b c
    valu _                                 = __IMPOSSIBLE__

instance EmbPrj FunctionInverse where
  icode NotInjective = icode0'
  icode (Inverse a)  = icode1' a
  value = vcase valu where valu []  = valu0 NotInjective
                           valu [a] = valu1 Inverse a
                           valu _   = __IMPOSSIBLE__

instance EmbPrj TermHead where
  icode SortHead    = icode0 0
  icode PiHead      = icode0 1
  icode (ConHead a) = icode1 2 a
  value = vcase valu where valu [0]    = return SortHead
                           valu [1]    = return PiHead
                           valu [2, a] = valu1 ConHead a
                           valu _      = __IMPOSSIBLE__

instance EmbPrj Agda.Syntax.Common.IsAbstract where
  icode AbstractDef = icode0 0
  icode ConcreteDef = icode0 1
  value = vcase valu where valu [0] = valu0 AbstractDef
                           valu [1] = valu0 ConcreteDef
                           valu _   = __IMPOSSIBLE__

instance EmbPrj I.Clause where
  icode (Clause a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Clause a b c d e
                           valu _            = __IMPOSSIBLE__

instance EmbPrj I.ClauseBody where
  icode (Body   a) = icode1 0 a
  icode (Bind   a) = icode1 1 a
  icode (NoBind a) = icode1 2 a
  icode NoBody     = icode0'
  value = vcase valu where valu [0, a] = valu1 Body   a
                           valu [1, a] = valu1 Bind   a
                           valu [2, a] = valu1 NoBind a
                           valu []     = valu0 NoBody
                           valu _      = __IMPOSSIBLE__

instance EmbPrj I.Pattern where
  icode (VarP a  ) = icode1 0 a
  icode (ConP a b) = icode2 1 a b
  icode (LitP a  ) = icode1 2 a
  icode (DotP a  ) = icode1 3 a
  value = vcase valu where valu [0, a]    = valu1 VarP a
                           valu [1, a, b] = valu2 ConP a b
                           valu [2, a]    = valu1 LitP a
                           valu [3, a]    = valu1 DotP a
                           valu _         = __IMPOSSIBLE__

instance EmbPrj a => EmbPrj (Builtin a) where
  icode (Prim    a) = icode1 0 a
  icode (Builtin a) = icode1 1 a
  value = vcase valu where valu [0, a] = valu1 Prim    a
                           valu [1, a] = valu1 Builtin a
                           valu _      = __IMPOSSIBLE__

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
    valu _       = __IMPOSSIBLE__

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
    valu _          = __IMPOSSIBLE__

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
    valu _   = __IMPOSSIBLE__

instance EmbPrj HP.MetaInfo where
  icode (HP.MetaInfo a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 HP.MetaInfo a b c d
    valu _            = __IMPOSSIBLE__

instance EmbPrj HP.HighlightingInfo where
  icode (HP.HighlightingInfo a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 HP.HighlightingInfo a b
    valu _      = __IMPOSSIBLE__

instance EmbPrj Interface where
  icode (Interface a b c d e f g) = icode7' a b c d e f g
  value = vcase valu where valu [a, b, c, d, e, f, g] = valu7 Interface a b c d e f g
                           valu _                     = __IMPOSSIBLE__



icodeX :: (Dict -> HashTable k Int) -> (Dict -> IORef Int) ->
          k -> S Int
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

vcase :: forall a . EmbPrj a => ([Int] -> R a) -> Int -> R a
vcase valu ix = do
    aTyp <- lift $ typeRepKey $ typeOf (undefined :: a)
    memo <- asks nodeMemo
    maybeU <- lift $ H.lookup memo (ix, aTyp)
    case maybeU of
      Just (U u) -> maybe (__IMPOSSIBLE__) return (cast u)
      Nothing    -> do
          v <- valu . (! ix) =<< asks nodeE 
          lift $ H.insert memo (ix, aTyp) (U v)
          return v

icode0  tag                     = icodeN [tag]
icode1  tag a                   = icodeN . (tag :) =<< sequence [icode a]
icode2  tag a b                 = icodeN . (tag :) =<< sequence [icode a, icode b]
icode3  tag a b c               = icodeN . (tag :) =<< sequence [icode a, icode b, icode c]
icode4  tag a b c d             = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d]
icode5  tag a b c d e           = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6  tag a b c d e f         = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7  tag a b c d e f g       = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8  tag a b c d e f g h     = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9  tag a b c d e f g h i   = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10 tag a b c d e f g h i j = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]

icode0'                      = icodeN []
icode1'  a                   = icodeN =<< sequence [icode a]
icode2'  a b                 = icodeN =<< sequence [icode a, icode b]
icode3'  a b c               = icodeN =<< sequence [icode a, icode b, icode c]
icode4'  a b c d             = icodeN =<< sequence [icode a, icode b, icode c, icode d]
icode5'  a b c d e           = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6'  a b c d e f         = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7'  a b c d e f g       = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8'  a b c d e f g h     = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9'  a b c d e f g h i   = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10' a b c d e f g h i j = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]

valu0  z                     = return z
valu1  z a                   = valu0 z                   `ap` value a
valu2  z a b                 = valu1 z a                 `ap` value b
valu3  z a b c               = valu2 z a b               `ap` value c
valu4  z a b c d             = valu3 z a b c             `ap` value d
valu5  z a b c d e           = valu4 z a b c d           `ap` value e
valu6  z a b c d e f         = valu5 z a b c d e         `ap` value f
valu7  z a b c d e f g       = valu6 z a b c d e f       `ap` value g
valu8  z a b c d e f g h     = valu7 z a b c d e f g     `ap` value h
valu9  z a b c d e f g h i   = valu8 z a b c d e f g h   `ap` value i
valu10 z a b c d e f g h i j = valu9 z a b c d e f g h i `ap` value j

test :: EmbPrj a => a -> IO a
test x = decode =<< encode x

emptyDict :: IO Dict
emptyDict = liftM5 Dict
            (H.new (==) hashNode)
            (H.new (==) H.hashString)
            (H.new (==) (H.hashInt . fromIntegral))
            (H.new (==) (H.hashInt . floor))
            (newIORef 0)
            `ap` (newIORef 0)
            `ap` (newIORef 0)
            `ap` (newIORef 0)

hashNode :: [ Int ] -> Int32
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

hashInt2 :: (Int, Int) -> Int32
hashInt2 (ix, rep) = hashNode [ix , rep]
