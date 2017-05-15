{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Internal where

import Control.Applicative
import Control.Monad.State.Strict

import Agda.Syntax.Internal as I
import Agda.Syntax.Position as P

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common ()
import Agda.TypeChecking.Serialise.Instances.Compilers ()

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Permutation

#include "undefined.h"
import Agda.Utils.Impossible

instance EmbPrj Signature where
  icod_ (Sig a b c) = icode3' a b c

  value = value3 Sig

instance EmbPrj Section where
  icod_ (Section a) = icode1' a

  value = value1 Section

instance EmbPrj a => EmbPrj (Tele a) where
  icod_ EmptyTel        = icode0'
  icod_ (ExtendTel a b) = icode2' a b

  value = vcase valu where
    valu []     = valuN EmptyTel
    valu [a, b] = valuN ExtendTel a b
    valu _      = malformed

instance EmbPrj Permutation where
  icod_ (Perm a b) = icode2' a b

  value = value2 Perm

instance EmbPrj a => EmbPrj (Drop a) where
  icod_ (Drop a b) = icode2' a b

  value = value2 Drop

instance EmbPrj a => EmbPrj (Elim' a) where
  icod_ (Apply a)  = icode1' a
  icod_ (Proj a b) = icode2 0 a b

  value = vcase valu where
    valu [a]       = valuN Apply a
    valu [0, a, b] = valuN Proj a b
    valu _         = malformed

instance EmbPrj I.ConHead where
  icod_ (ConHead a b c) = icode3' a b c

  value = value3 ConHead

instance (EmbPrj a) => EmbPrj (I.Type' a) where
  icod_ (El a b) = icode2' a b

  value = value2 El

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icod_ (NoAbs a b) = icode2 0 a b
  icod_ (Abs a b)   = icode2' a b

  value = vcase valu where
    valu [a, b]    = valuN Abs a b
    valu [0, a, b] = valuN NoAbs a b
    valu _         = malformed

instance EmbPrj I.Term where
  icod_ (Var     a []) = icode1' a
  icod_ (Var      a b) = icode2 0 a b
  icod_ (Lam      a b) = icode2 1 a b
  icod_ (Lit      a  ) = icode1 2 a
  icod_ (Def      a b) = icode2 3 a b
  icod_ (Con    a b c) = icode3 4 a b c
  icod_ (Pi       a b) = icode2 5 a b
  icod_ (Sort     a  ) = icode1 7 a
  icod_ (MetaV    a b) = icode2 8 a b
  icod_ (DontCare a  ) = icode1 9 a
  icod_ (Level    a  ) = icode1 10 a
  icod_ (Shared p)     = icodeMemo termD termC p $ icode (derefPtr p)

  value r = vcase valu' r where
    valu' xs       = gets mkShared <*> valu xs
    valu [a]       = valuN var   a
    valu [0, a, b] = valuN Var   a b
    valu [1, a, b] = valuN Lam   a b
    valu [2, a]    = valuN Lit   a
    valu [3, a, b] = valuN Def   a b
    valu [4, a, b, c] = valuN Con a b c
    valu [5, a, b] = valuN Pi    a b
    valu [7, a]    = valuN Sort  a
    valu [8, a, b] = valuN MetaV a b
    valu [9, a]    = valuN DontCare a
    valu [10, a]   = valuN Level a
    valu _         = malformed

instance EmbPrj Level where
  icod_ (Max a) = icode1' a

  value = value1 Max

instance EmbPrj PlusLevel where
  icod_ (ClosedLevel a) = icode1' a
  icod_ (Plus a b)      = icode2' a b

  value = vcase valu where
    valu [a]    = valuN ClosedLevel a
    valu [a, b] = valuN Plus a b
    valu _      = malformed

instance EmbPrj LevelAtom where
  icod_ (NeutralLevel _ a) = icode1' a
  icod_ (UnreducedLevel a) = icode1 1 a
  icod_ (MetaLevel a b)    = icode2 2 a b
  icod_ BlockedLevel{}     = __IMPOSSIBLE__

  value = vcase valu where
    valu [a]    = valuN UnreducedLevel a -- we forget that we are a NeutralLevel,
                                         -- since we do not want do (de)serialize
                                         -- the reason for neutrality
    valu [1, a] = valuN UnreducedLevel a
    valu [2, a, b] = valuN MetaLevel a b
    valu _      = malformed

instance EmbPrj I.Sort where
  icod_ (Type  a  ) = icode1' a
  icod_ Prop        = icode1 1 ()
  icod_ SizeUniv    = icode1 3 ()
  icod_ Inf         = icode1 4 ()
  icod_ (DLub a b)  = icode2 2 a b -- Andreas, 2017-01-18: not __IMPOSSIBLE__ see #2408

  value = vcase valu where
    valu [a]    = valuN Type  a
    valu [1, _] = valuN Prop
    valu [3, _] = valuN SizeUniv
    valu [4, _] = valuN Inf
    valu [2, a, b] = valuN DLub a b
    valu _         = malformed

instance EmbPrj DisplayForm where
  icod_ (Display a b c) = icode3' a b c

  value = value3 Display

instance EmbPrj a => EmbPrj (Open a) where
  icod_ (OpenThing a b) = icode2' a b

  value = value2 OpenThing

instance EmbPrj a => EmbPrj (Local a) where
  icod_ (Local a b) = icode2' a b
  icod_ (Global a)  = icode1' a

  value = vcase valu where
    valu [a, b] = valuN Local a b
    valu [a]    = valuN Global a
    valu _      = malformed

instance EmbPrj CtxId where
  icod_ (CtxId a) = icode a
  value n         = CtxId `fmap` value n

instance EmbPrj DisplayTerm where
  icod_ (DTerm    a  )   = icode1' a
  icod_ (DDot     a  )   = icode1 1 a
  icod_ (DCon     a b c) = icode3 2 a b c
  icod_ (DDef     a b)   = icode2 3 a b
  icod_ (DWithApp a b c) = icode3 4 a b c

  value = vcase valu where
    valu [a]          = valuN DTerm a
    valu [1, a]       = valuN DDot a
    valu [2, a, b, c] = valuN DCon a b c
    valu [3, a, b]    = valuN DDef a b
    valu [4, a, b, c] = valuN DWithApp a b c
    valu _            = malformed

instance EmbPrj MutualId where
  icod_ (MutId a) = icode a
  value n         = MutId `fmap` value n

instance EmbPrj Definition where
  icod_ (Defn a b c d e f g h i j k l m) = icode13' a b (P.killRange c) d e f g h i j k l m

  value = vcase valu where
    valu [a, b, c, d, e, f, g, h, i, j, k, l, m] = valuN Defn a b c d e f g h i j k l m
    valu _                                       = malformed

instance EmbPrj NLPat where
  icod_ (PVar a b c)    = icode3 0 a b c
  icod_ (PWild)         = icode0 1
  icod_ (PDef a b)      = icode2 2 a b
  icod_ (PLam a b)      = icode2 3 a b
  icod_ (PPi a b)       = icode2 4 a b
  icod_ (PBoundVar a b) = icode2 5 a b
  icod_ (PTerm a)       = icode1 6 a

  value = vcase valu where
    valu [0, a, b, c] = valuN PVar a b c
    valu [1]          = valuN PWild
    valu [2, a, b]    = valuN PDef a b
    valu [3, a, b]    = valuN PLam a b
    valu [4, a, b]    = valuN PPi a b
    valu [5, a, b]    = valuN PBoundVar a b
    valu [6, a]       = valuN PTerm a
    valu _            = malformed

instance EmbPrj NLPType where
  icod_ (NLPType a b) = icode2' a b

  value = value2 NLPType

instance EmbPrj RewriteRule where
  icod_ (RewriteRule a b c d e f) = icode6' a b c d e f

  value = value6 RewriteRule

instance EmbPrj Projection where
  icod_ (Projection a b c d e) = icode5' a b c d e

  value = value5 Projection

instance EmbPrj ProjLams where
  icod_ (ProjLams a) = icode1' a

  value = value1 ProjLams

instance EmbPrj ExtLamInfo where
  icod_ (ExtLamInfo a b) = icode2' a b

  value = value2 ExtLamInfo

instance EmbPrj Polarity where
  icod_ Covariant     = return 0
  icod_ Contravariant = return 1
  icod_ Invariant     = return 2
  icod_ Nonvariant    = return 3

  value 0 = return Covariant
  value 1 = return Contravariant
  value 2 = return Invariant
  value 3 = return Nonvariant
  value _ = malformed

instance EmbPrj Occurrence where
  icod_ StrictPos = return 0
  icod_ Mixed     = return 1
  icod_ Unused    = return 2
  icod_ GuardPos  = return 3
  icod_ JustPos   = return 4
  icod_ JustNeg   = return 5

  value 0 = return StrictPos
  value 1 = return Mixed
  value 2 = return Unused
  value 3 = return GuardPos
  value 4 = return JustPos
  value 5 = return JustNeg
  value _ = malformed

instance EmbPrj EtaEquality where
  icod_ (Specified a) = icode1 0 a
  icod_ (Inferred a)  = icode1 1 a

  value = vcase valu where
    valu [0,a] = valuN Specified a
    valu [1,a] = valuN Inferred a
    valu _     = malformed

instance EmbPrj Defn where
  icod_ Axiom                                   = icode0 0
  icod_ (Function    a b _ c d e f g h i j k m) = icode12 1 a b c d e f g h i j k m
  icod_ (Datatype    a b c d e f g h i j)       = icode10 2 a b c d e f g h i j
  icod_ (Record      a b c d e f g h i j)       = icode10 3 a b c d e f g h i j
  icod_ (Constructor a b c d e f g)             = icode7 4 a b c d e f g
  icod_ (Primitive   a b c d)                   = icode4 5 a b c d
  icod_ AbstractDefn                            = __IMPOSSIBLE__

  value = vcase valu where
    valu [0]                                     = valuN Axiom
    valu [1, a, b, c, d, e, f, g, h, i, j, k, m] = valuN (\ a b -> Function a b Nothing) a b c d e f g h i j k m
    valu [2, a, b, c, d, e, f, g, h, i, j]       = valuN Datatype a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h, i, j]       = valuN Record  a b c d e f g h i j
    valu [4, a, b, c, d, e, f, g]                = valuN Constructor a b c d e f g
    valu [5, a, b, c, d]                         = valuN Primitive   a b c d
    valu _                                       = malformed

instance EmbPrj FunctionFlag where
  icod_ FunStatic       = icode0 0
  icod_ FunInline       = icode0 1
  icod_ FunMacro        = icode0 2

  value = vcase valu where
    valu [0] = valuN FunStatic
    valu [1] = valuN FunInline
    valu [2] = valuN FunMacro
    valu _   = malformed

instance EmbPrj a => EmbPrj (WithArity a) where
  icod_ (WithArity a b) = icode2' a b

  value = value2 WithArity

instance EmbPrj a => EmbPrj (Case a) where
  icod_ (Branches a b c d) = icode4' a b c d

  value = value4 Branches

instance EmbPrj CompiledClauses where
  icod_ Fail       = icode0'
  icod_ (Done a b) = icode2' a (P.killRange b)
  icod_ (Case a b) = icode2 2 a b

  value = vcase valu where
    valu []        = valuN Fail
    valu [a, b]    = valuN Done a b
    valu [2, a, b] = valuN Case a b
    valu _         = malformed

instance EmbPrj a => EmbPrj (FunctionInverse' a) where
  icod_ NotInjective = icode0'
  icod_ (Inverse a)  = icode1' a

  value = vcase valu where
    valu []  = valuN NotInjective
    valu [a] = valuN Inverse a
    valu _   = malformed

instance EmbPrj TermHead where
  icod_ SortHead     = icode0'
  icod_ PiHead       = icode0 1
  icod_ (ConsHead a) = icode1 2 a

  value = vcase valu where
    valu []     = valuN SortHead
    valu [1]    = valuN PiHead
    valu [2, a] = valuN ConsHead a
    valu _      = malformed

instance EmbPrj I.Clause where
  icod_ (Clause a b c d e f g) = icode7' a b c d e f g

  value = value7 Clause

instance EmbPrj I.ConPatternInfo where
  icod_ (ConPatternInfo a b) = icode2' a b

  value = value2 ConPatternInfo

instance EmbPrj I.DBPatVar where
  icod_ (DBPatVar a b) = icode2' a b

  value = value2 DBPatVar

instance EmbPrj a => EmbPrj (I.Pattern' a) where
  icod_ (VarP a    ) = icode1' a
  icod_ (ConP a b c) = icode3 1 a b c
  icod_ (LitP a    ) = icode1 2 a
  icod_ (DotP a    ) = icode1 3 a
  icod_ (ProjP a b ) = icode2 4 a b
  icod_ (AbsurdP a ) = icode1 5 a

  value = vcase valu where
    valu [a]       = valuN VarP a
    valu [1, a, b, c] = valuN ConP a b c
    valu [2, a]    = valuN LitP a
    valu [3, a]    = valuN DotP a
    valu [4, a, b] = valuN ProjP a b
    valu [5, a]    = valuN AbsurdP a
    valu _         = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icod_ (Prim    a) = icode1' a
  icod_ (Builtin a) = icode1 1 a

  value = vcase valu where
    valu [a]    = valuN Prim    a
    valu [1, a] = valuN Builtin a
    valu _      = malformed

instance EmbPrj a => EmbPrj (Substitution' a) where
  icod_ IdS              = icode0'
  icod_ EmptyS           = icode0 1
  icod_ (a :# b)         = icode2 2 a b
  icod_ (Strengthen a b) = icode2 3 a b
  icod_ (Wk a b)         = icode2 4 a b
  icod_ (Lift a b)       = icode2 5 a b

  value = vcase valu where
    valu []        = valuN IdS
    valu [1]       = valuN EmptyS
    valu [2, a, b] = valuN (:#) a b
    valu [3, a, b]    = valuN Strengthen a b
    valu [4, a, b] = valuN Wk a b
    valu [5, a, b] = valuN Lift a b
    valu _         = malformed
