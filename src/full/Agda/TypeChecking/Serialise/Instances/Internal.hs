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

  value = vcase valu where
    valu [a, b, c] = valu3 Sig a b c
    valu _         = malformed

instance EmbPrj Section where
  icod_ (Section a) = icode1' a

  value = vcase valu where
    valu [a] = valu1 Section a
    valu _   = malformed

instance EmbPrj a => EmbPrj (Tele a) where
  icod_ EmptyTel        = icode0'
  icod_ (ExtendTel a b) = icode2' a b

  value = vcase valu where
    valu []     = valu0 EmptyTel
    valu [a, b] = valu2 ExtendTel a b
    valu _      = malformed

instance EmbPrj Permutation where
  icod_ (Perm a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 Perm a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Drop a) where
  icod_ (Drop a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 Drop a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Elim' a) where
  icod_ (Apply a)  = icode1' a
  icod_ (Proj a b) = icode2 0 a b

  value = vcase valu where
    valu [a]       = valu1 Apply a
    valu [0, a, b] = valu2 Proj a b
    valu _         = malformed

instance EmbPrj I.ConHead where
  icod_ (ConHead a b c) = icode3' a b c

  value = vcase valu where
    valu [a, b, c] = valu3 ConHead a b c
    valu _         = malformed

instance (EmbPrj a) => EmbPrj (I.Type' a) where
  icod_ (El a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 El a b
    valu _      = malformed

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icod_ (NoAbs a b) = icode2 0 a b
  icod_ (Abs a b)   = icode2' a b

  value = vcase valu where
    valu [a, b]    = valu2 Abs a b
    valu [0, a, b] = valu2 NoAbs a b
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
  icod_ (MetaV    a b) = __IMPOSSIBLE__
  icod_ (DontCare a  ) = icode1 8 a
  icod_ (Level    a  ) = icode1 9 a
  icod_ (Shared p)     = icodeMemo termD termC p $ icode (derefPtr p)

  value r = vcase valu' r where
    valu' xs       = gets mkShared <*> valu xs
    valu [a]       = valu1 var   a
    valu [0, a, b] = valu2 Var   a b
    valu [1, a, b] = valu2 Lam   a b
    valu [2, a]    = valu1 Lit   a
    valu [3, a, b] = valu2 Def   a b
    valu [4, a, b, c] = valu3 Con a b c
    valu [5, a, b] = valu2 Pi    a b
    valu [7, a]    = valu1 Sort  a
    valu [8, a]    = valu1 DontCare a
    valu [9, a]    = valu1 Level a
    valu _         = malformed

instance EmbPrj Level where
  icod_ (Max a) = icode1' a

  value = vcase valu where
    valu [a] = valu1 Max a
    valu _   = malformed

instance EmbPrj PlusLevel where
  icod_ (ClosedLevel a) = icode1' a
  icod_ (Plus a b)      = icode2' a b

  value = vcase valu where
    valu [a]    = valu1 ClosedLevel a
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
  icod_ (DLub a b)  = icode2 2 a b -- Andreas, 2017-01-18: not __IMPOSSIBLE__ see #2408

  value = vcase valu where
    valu [a]    = valu1 Type  a
    valu [1, _] = valu0 Prop
    valu [3, _] = valu0 SizeUniv
    valu [4, _] = valu0 Inf
    valu [2, a, b] = valu2 DLub a b
    valu _         = malformed

instance EmbPrj DisplayForm where
  icod_ (Display a b c) = icode3' a b c

  value = vcase valu where
    valu [a, b, c] = valu3 Display a b c
    valu _         = malformed

instance EmbPrj a => EmbPrj (Open a) where
  icod_ (OpenThing a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 OpenThing a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Local a) where
  icod_ (Local a b) = icode2' a b
  icod_ (Global a)  = icode1' a

  value = vcase valu where
    valu [a, b] = valu2 Local a b
    valu [a]    = valu1 Global a
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
    valu [a]          = valu1 DTerm a
    valu [1, a]       = valu1 DDot a
    valu [2, a, b, c] = valu3 DCon a b c
    valu [3, a, b]    = valu2 DDef a b
    valu [4, a, b, c] = valu3 DWithApp a b c
    valu _            = malformed

instance EmbPrj MutualId where
  icod_ (MutId a) = icode a
  value n         = MutId `fmap` value n

instance EmbPrj Definition where
  icod_ (Defn a b c d e f g h i j k l m) = icode13' a b (P.killRange c) d e f g h i j k l m

  value = vcase valu where
    valu [a, b, c, d, e, f, g, h, i, j, k, l, m] = valu13 Defn a b c d e f g h i j k l m
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
    valu [0, a, b, c] = valu3 PVar a b c
    valu [1]          = valu0 PWild
    valu [2, a, b]    = valu2 PDef a b
    valu [3, a, b]    = valu2 PLam a b
    valu [4, a, b]    = valu2 PPi a b
    valu [5, a, b]    = valu2 PBoundVar a b
    valu [6, a]       = valu1 PTerm a
    valu _            = malformed

instance EmbPrj NLPType where
  icod_ (NLPType a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 NLPType a b
    valu _      = malformed

instance EmbPrj RewriteRule where
  icod_ (RewriteRule a b c d e f) = icode6' a b c d e f

  value = vcase valu where
    valu [a, b, c, d, e, f] = valu6 RewriteRule a b c d e f
    valu _                  = malformed

instance EmbPrj Projection where
  icod_ (Projection a b c d e) = icode5' a b c d e

  value = vcase valu where
    valu [a, b, c, d, e] = valu5 Projection a b c d e
    valu _ = malformed

instance EmbPrj ProjLams where
  icod_ (ProjLams a) = icode1' a

  value = vcase valu where
    valu [a] = valu1 ProjLams a
    valu _   = malformed

instance EmbPrj ExtLamInfo where
  icod_ (ExtLamInfo a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 ExtLamInfo a b
    valu _      = malformed

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
    valu [0,a] = valu1 Specified a
    valu [1,a] = valu1 Inferred a
    valu _     = malformed

instance EmbPrj Defn where
  icod_ Axiom                                   = icode0 0
  icod_ (Function    a b _ c d e f g h i j k m) = icode12 1 a b c d e f g h i j k m
  icod_ (Datatype    a b c d e f g h i j)       = icode10 2 a b c d e f g h i j
  icod_ (Record      a b c d e f g h i j k)     = icode11 3 a b c d e f g h i j k
  icod_ (Constructor a b c d e f)               = icode6 4 a b c d e f
  icod_ (Primitive   a b c d)                   = icode4 5 a b c d
  icod_ AbstractDefn                            = __IMPOSSIBLE__

  value = vcase valu where
    valu [0]                                     = valu0 Axiom
    valu [1, a, b, c, d, e, f, g, h, i, j, k, m] = valu12 (\ a b -> Function a b Nothing) a b c d e f g h i j k m
    valu [2, a, b, c, d, e, f, g, h, i, j]       = valu10 Datatype a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h, i, j, k]    = valu11 Record  a b c d e f g h i j k
    valu [4, a, b, c, d, e, f]                   = valu6 Constructor a b c d e f
    valu [5, a, b, c, d]                         = valu4 Primitive   a b c d
    valu _                                       = malformed

instance EmbPrj FunctionFlag where
  icod_ FunStatic       = icode0 0
  icod_ FunInline       = icode0 1
  icod_ FunMacro        = icode0 2

  value = vcase valu where
    valu [0] = valu0 FunStatic
    valu [1] = valu0 FunInline
    valu [2] = valu0 FunMacro
    valu _   = malformed

instance EmbPrj a => EmbPrj (WithArity a) where
  icod_ (WithArity a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 WithArity a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Case a) where
  icod_ (Branches a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 Branches a b c d
    valu _            = malformed

instance EmbPrj CompiledClauses where
  icod_ Fail       = icode0'
  icod_ (Done a b) = icode2' a (P.killRange b)
  icod_ (Case a b) = icode2 2 a b

  value = vcase valu where
    valu []        = valu0 Fail
    valu [a, b]    = valu2 Done a b
    valu [2, a, b] = valu2 Case a b
    valu _         = malformed

instance EmbPrj a => EmbPrj (FunctionInverse' a) where
  icod_ NotInjective = icode0'
  icod_ (Inverse a)  = icode1' a

  value = vcase valu where
    valu []  = valu0 NotInjective
    valu [a] = valu1 Inverse a
    valu _   = malformed

instance EmbPrj TermHead where
  icod_ SortHead     = icode0'
  icod_ PiHead       = icode0 1
  icod_ (ConsHead a) = icode1 2 a

  value = vcase valu where
    valu []     = valu0 SortHead
    valu [1]    = valu0 PiHead
    valu [2, a] = valu1 ConsHead a
    valu _      = malformed

instance EmbPrj I.Clause where
  icod_ (Clause a b c d e f) = icode6' a b c d e f

  value = vcase valu where
    valu [a, b, c, d, e, f] = valu6 Clause a b c d e f
    valu _                  = malformed

instance EmbPrj I.ConPatternInfo where
  icod_ (ConPatternInfo a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 ConPatternInfo a b
    valu _      = malformed

instance EmbPrj I.DBPatVar where
  icod_ (DBPatVar a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 DBPatVar a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (I.Pattern' a) where
  icod_ (VarP a    ) = icode1' a
  icod_ (ConP a b c) = icode3 1 a b c
  icod_ (LitP a    ) = icode1 2 a
  icod_ (DotP a    ) = icode1 3 a
  icod_ (ProjP a b ) = icode2 4 a b

  value = vcase valu where
    valu [a]       = valu1 VarP a
    valu [1, a, b, c] = valu3 ConP a b c
    valu [2, a]    = valu1 LitP a
    valu [3, a]    = valu1 DotP a
    valu [4, a, b] = valu2 ProjP a b
    valu _         = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icod_ (Prim    a) = icode1' a
  icod_ (Builtin a) = icode1 1 a

  value = vcase valu where
    valu [a]    = valu1 Prim    a
    valu [1, a] = valu1 Builtin a
    valu _      = malformed
