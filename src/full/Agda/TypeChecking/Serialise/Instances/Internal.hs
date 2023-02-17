
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Internal where

import qualified Data.HashSet as HashSet
import Control.Monad
import Control.Monad.IO.Class

import Agda.Syntax.Internal as I
import Agda.Syntax.Position as P

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Compilers () --instance only

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Coverage.SplitTree

import Agda.Termination.TypeBased.Syntax ( SizeSignature (..), SizeTele (..), Size (..), SizeBound (..) )

import Agda.Utils.Functor
import Agda.Utils.Permutation

import Agda.Utils.Impossible

instance EmbPrj a => EmbPrj (Dom a) where
  icod_ (Dom a c d e f) = icodeN' Dom a c d e f

  value = valueN Dom

instance EmbPrj Signature where
  icod_ (Sig a b c) = icodeN' Sig a b c

  value = valueN Sig

instance EmbPrj Section where
  icod_ (Section a) = icodeN' Section a

  value = valueN Section

instance EmbPrj a => EmbPrj (Tele a) where
  icod_ EmptyTel        = icodeN' EmptyTel
  icod_ (ExtendTel a b) = icodeN' ExtendTel a b

  value = vcase valu where
    valu []     = valuN EmptyTel
    valu [a, b] = valuN ExtendTel a b
    valu _      = malformed

instance EmbPrj Permutation where
  icod_ (Perm a b) = icodeN' Perm a b

  value = valueN Perm

instance EmbPrj a => EmbPrj (Drop a) where
  icod_ (Drop a b) = icodeN' Drop a b

  value = valueN Drop

instance EmbPrj a => EmbPrj (Elim' a) where
  icod_ (Apply a)      = icodeN' Apply a
  icod_ (IApply x y a) = icodeN 0 IApply x y a
  icod_ (Proj a b)     = icodeN 0 Proj a b

  value = vcase valu where
    valu [a]       = valuN Apply a
    valu [0,x,y,a] = valuN IApply x y a
    valu [0, a, b] = valuN Proj a b
    valu _         = malformed

instance EmbPrj I.DataOrRecord where
  icod_ = \case
    IsData      -> icodeN' IsData
    IsRecord pm -> icodeN' IsRecord pm

  value = vcase $ \case
    []   -> valuN IsData
    [pm] -> valuN IsRecord pm
    _    -> malformed

instance EmbPrj I.ConHead where
  icod_ (ConHead a b c d) = icodeN' ConHead a b c d

  value = valueN ConHead

instance (EmbPrj a) => EmbPrj (I.Type' a) where
  icod_ (El a b) = icodeN' El a b

  value = valueN El

instance EmbPrj a => EmbPrj (I.Abs a) where
  icod_ (NoAbs a b) = icodeN 0 NoAbs a b
  icod_ (Abs a b)   = icodeN' Abs a b

  value = vcase valu where
    valu [a, b]    = valuN Abs a b
    valu [0, a, b] = valuN NoAbs a b
    valu _         = malformed

instance EmbPrj I.Term where
  icod_ (Var     a []) = icodeN' (\ a -> Var a []) a
  icod_ (Var      a b) = icodeN 0 Var a b
  icod_ (Lam      a b) = icodeN 1 Lam a b
  icod_ (Lit      a  ) = icodeN 2 Lit a
  icod_ (Def      a b) = icodeN 3 Def a b
  icod_ (Con    a b c) = icodeN 4 Con a b c
  icod_ (Pi       a b) = icodeN 5 Pi a b
  icod_ (MetaV    a b) = icodeN 6 MetaV a b
  icod_ (Sort     a  ) = icodeN 7 Sort a
  icod_ (DontCare a  ) = icodeN 8 DontCare a
  icod_ (Level    a  ) = icodeN 9 Level a
  icod_ (Dummy    a b) = icodeN 10 Dummy a b

  value = vcase valu where
    valu [a]       = valuN var   a
    valu [0, a, b] = valuN Var   a b
    valu [1, a, b] = valuN Lam   a b
    valu [2, a]    = valuN Lit   a
    valu [3, a, b] = valuN Def   a b
    valu [4, a, b, c] = valuN Con a b c
    valu [5, a, b] = valuN Pi    a b
    valu [6, a, b] = valuN MetaV a b
    valu [7, a]    = valuN Sort  a
    valu [8, a]    = valuN DontCare a
    valu [9, a]    = valuN Level a
    valu [10, a, b] = valuN Dummy a b
    valu _         = malformed

instance EmbPrj Level where
  icod_ (Max a b) = icodeN' Max a b

  value = valueN Max

instance EmbPrj PlusLevel where
  icod_ (Plus a b) = icodeN' Plus a b

  value = valueN Plus

instance EmbPrj IsFibrant where
  icod_ IsFibrant = return 0
  icod_ IsStrict  = return 1

  value 0 = return IsFibrant
  value 1 = return IsStrict
  value _ = malformed

instance EmbPrj Univ where

instance EmbPrj I.Sort where
  icod_ = \case
    Univ a b     -> icodeN 0  Univ a b
    SizeUniv     -> icodeN 2  SizeUniv
    Inf a b      -> icodeN 3  Inf a b
    PiSort a b c -> icodeN 4  PiSort a b c
    FunSort a b  -> icodeN 5  FunSort a b
    UnivSort a   -> icodeN 6  UnivSort a
    DefS a b     -> icodeN 7  DefS a b
    LockUniv     -> icodeN 9  LockUniv
    IntervalUniv -> icodeN 10 IntervalUniv
    MetaS a b    -> icodeN 11 MetaS a b
    DummyS s     -> icodeN 12 DummyS s
    LevelUniv    -> icodeN 13 LevelUniv

  value = vcase valu where
    valu [0, a, b] = valuN Univ a b
    valu [2]       = valuN SizeUniv
    valu [3, a, b] = valuN Inf a b
    valu [4, a, b, c] = valuN PiSort a b c
    valu [5, a, b] = valuN FunSort a b
    valu [6, a]    = valuN UnivSort a
    valu [7, a, b] = valuN DefS a b
    valu [9]       = valuN LockUniv
    valu [10]      = valuN IntervalUniv
    valu [11, a, b] = valuN MetaS a b
    valu [12, s]   = valuN DummyS s
    valu [13]      = valuN LevelUniv
    valu _         = malformed

instance EmbPrj DisplayForm where
  icod_ (Display a b c) = icodeN' Display a b c

  value = valueN Display

instance EmbPrj a => EmbPrj (Open a) where
  icod_ (OpenThing a b c d) = icodeN' OpenThing a b c d

  value = valueN OpenThing

instance EmbPrj CheckpointId where
  icod_ (CheckpointId a) = icode a
  value n                = CheckpointId <$!> value n

instance EmbPrj DisplayTerm where
  icod_ (DTerm'   a b)   = icodeN' DTerm' a b
  icod_ (DDot'    a b)   = icodeN 1 DDot' a b
  icod_ (DCon     a b c) = icodeN 2 DCon a b c
  icod_ (DDef     a b)   = icodeN 3 DDef a b
  icod_ (DWithApp a b c) = icodeN 4 DWithApp a b c

  value = vcase valu where
    valu [a, b]       = valuN DTerm' a b
    valu [1, a, b]    = valuN DDot' a b
    valu [2, a, b, c] = valuN DCon a b c
    valu [3, a, b]    = valuN DDef a b
    valu [4, a, b, c] = valuN DWithApp a b c
    valu _            = malformed

instance EmbPrj MutualId where
  icod_ (MutId a) = icode a
  value n         = MutId <$!> value n

instance EmbPrj CompKit where
  icod_ (CompKit a b) = icodeN' CompKit a b
  value = valueN CompKit

instance EmbPrj SizeSignature where
  icod_ (SizeSignature a b c) = icodeN' SizeSignature a b c
  value = vcase valu where
    valu [a, b, c] = valuN SizeSignature a b c
    valu _      = malformed

instance EmbPrj SizeBound where
  icod_ SizeUnbounded = icodeN' SizeUnbounded
  icod_ (SizeBounded i) = icodeN 0 SizeBounded i

  value = vcase valu where
    valu []     = valuN SizeUnbounded
    valu [0, a] = valuN SizeBounded a
    valu _      = malformed

instance EmbPrj SizeTele where
  icod_ (SizeTree a b)      = icodeN 0 SizeTree a b
  icod_ (SizeArrow a b)     = icodeN 1 SizeArrow a b
  icod_ (SizeGeneric a b c) = icodeN 2 SizeGeneric a b c
  icod_ (SizeGenericVar a b)  = icodeN 3 SizeGenericVar a b

  value = vcase valu where
    valu [0, a, b]    = valuN SizeTree a b
    valu [1, a, b]    = valuN SizeArrow a b
    valu [2, a, b, c] = valuN SizeGeneric a b c
    valu [3, a, b]    = valuN SizeGenericVar a b
    valu _            = malformed

instance EmbPrj Size where
  icod_ (SUndefined) = icodeN' SUndefined
  icod_ (SDefined i) = icodeN 0 SDefined i

  value = vcase valu where
    valu [] = valuN SUndefined
    valu [0, i] = valuN SDefined i
    valu _      = malformed

instance EmbPrj Definition where
  icod_ (Defn a b c d e f g h i j k l m n o p r blocked s t) =
    icodeN' Defn a b (P.killRange c) d e f g h i j k l m n o p r (ossify blocked) s t
    where
      -- Andreas, 2024-01-02, issue #7044:
      -- After serialization, a definition can never be unblocked,
      -- since all metas are ossified.
      -- Thus, we turn any blocker into 'neverUnblock'.
      ossify :: Blocked_ -> Blocked_
      ossify = \case
        b@NotBlocked{} -> b
        Blocked b () -> Blocked neverUnblock ()
  value = valueN Defn

instance EmbPrj NotBlocked where
  icod_ ReallyNotBlocked = icodeN' ReallyNotBlocked
  icod_ (StuckOn a)      = icodeN 0 StuckOn a
  icod_ Underapplied     = icodeN 1 Underapplied
  icod_ AbsurdMatch      = icodeN 2 AbsurdMatch
  icod_ (MissingClauses a) = icodeN 3 MissingClauses a

  value = vcase valu where
    valu []     = valuN ReallyNotBlocked
    valu [0, a] = valuN StuckOn a
    valu [1]    = valuN Underapplied
    valu [2]    = valuN AbsurdMatch
    valu [3, a] = valuN MissingClauses a
    valu _      = malformed

-- Andreas, 2024-01-02, issue #7044.
-- We only serialize 'neverUnblock';
-- other than that, there should not be any blockers left at serialization time.
blockedToMaybe :: Blocked_ -> Maybe NotBlocked
blockedToMaybe = \case
  NotBlocked a ()       -> Just a
  Blocked a ()
    | a == neverUnblock -> Nothing
    | otherwise         -> __IMPOSSIBLE__

blockedFromMaybe :: Maybe NotBlocked -> Blocked_
blockedFromMaybe = maybe (Blocked neverUnblock ()) (`NotBlocked` ())

instance EmbPrj Blocked_ where
  icod_ = icod_ . blockedToMaybe
  value = blockedFromMaybe <.> value

instance EmbPrj NLPat where
  icod_ (PVar a b)      = icodeN 0 PVar a b
  icod_ (PDef a b)      = icodeN 1 PDef a b
  icod_ (PLam a b)      = icodeN 2 PLam a b
  icod_ (PPi a b)       = icodeN 3 PPi a b
  icod_ (PSort a)       = icodeN 4 PSort a
  icod_ (PBoundVar a b) = icodeN 5 PBoundVar a b
  icod_ (PTerm a)       = icodeN 6 PTerm a

  value = vcase valu where
    valu [0, a, b]    = valuN PVar a b
    valu [1, a, b]    = valuN PDef a b
    valu [2, a, b]    = valuN PLam a b
    valu [3, a, b]    = valuN PPi a b
    valu [4, a]       = valuN PSort a
    valu [5, a, b]    = valuN PBoundVar a b
    valu [6, a]       = valuN PTerm a
    valu _            = malformed

instance EmbPrj NLPType where
  icod_ (NLPType a b) = icodeN' NLPType a b

  value = valueN NLPType

instance EmbPrj NLPSort where
  icod_ (PType a)   = icodeN 0 PType a
  icod_ (PProp a)   = icodeN 1 PProp a
  icod_ (PInf f a)  = icodeN 2 PInf f a
  icod_ PSizeUniv   = icodeN 3 PSizeUniv
  icod_ PLockUniv   = icodeN 4 PLockUniv
  icod_ PIntervalUniv = icodeN 5 PIntervalUniv
  icod_ (PSSet a)   = icodeN 6 PSSet a
  icod_ PLevelUniv = icodeN 7 PLevelUniv

  value = vcase valu where
    valu [0, a] = valuN PType a
    valu [1, a] = valuN PProp a
    valu [2, f, a] = valuN PInf f a
    valu [3]    = valuN PSizeUniv
    valu [4]    = valuN PLockUniv
    valu [5]    = valuN PIntervalUniv
    valu [6, a] = valuN PSSet a
    valu [7]    = valuN PLevelUniv
    valu _      = malformed

instance EmbPrj RewriteRule where
  icod_ (RewriteRule a b c d e f g) = icodeN' RewriteRule a b c d e f g

  value = valueN RewriteRule

instance EmbPrj Projection where
  icod_ (Projection a b c d e) = icodeN' Projection a b c d e

  value = valueN Projection

instance EmbPrj ProjLams where
  icod_ (ProjLams a) = icodeN' ProjLams a

  value = valueN ProjLams

instance EmbPrj System where
  icod_ (System a b) = icodeN' System a b

  value = valueN System

instance EmbPrj ExtLamInfo where
  icod_ (ExtLamInfo a b c) = icodeN' ExtLamInfo a b c

  value = valueN ExtLamInfo

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

instance EmbPrj IsForced where
  icod_ Forced    = return 0
  icod_ NotForced = return 1

  value 0 = return Forced
  value 1 = return NotForced
  value _ = malformed

instance EmbPrj NumGeneralizableArgs where
  icod_ NoGeneralizableArgs       = icodeN' NoGeneralizableArgs
  icod_ (SomeGeneralizableArgs a) = icodeN' SomeGeneralizableArgs a

  value = vcase valu where
    valu []  = valuN NoGeneralizableArgs
    valu [a] = valuN SomeGeneralizableArgs a
    valu _   = malformed

instance EmbPrj DoGeneralize where
  icod_ YesGeneralizeVar  = return 0
  icod_ YesGeneralizeMeta = return 1
  icod_ NoGeneralize      = return 2

  value 0 = return YesGeneralizeVar
  value 1 = return YesGeneralizeMeta
  value 2 = return NoGeneralize
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
  icod_ (Specified a) = icodeN 0 Specified a
  icod_ (Inferred a)  = icodeN 1 Inferred a

  value = vcase valu where
    valu [0,a] = valuN Specified a
    valu [1,a] = valuN Inferred a
    valu _     = malformed

instance EmbPrj ProjectionLikenessMissing

instance EmbPrj BuiltinSort where
  icod_ = \case
    SortUniv  a      -> icodeN 0 SortUniv  a
    SortOmega a      -> icodeN 1 SortOmega a
    SortIntervalUniv -> icodeN 2 SortIntervalUniv
    SortLevelUniv    -> icodeN 3 SortLevelUniv

  value = vcase \case
    [0, a] -> valuN SortUniv  a
    [1, a] -> valuN SortOmega a
    [2]    -> valuN SortIntervalUniv
    [3]    -> valuN SortLevelUniv
    _ -> malformed

instance EmbPrj Defn where
  icod_ (Axiom       a)                                 = icodeN 0 Axiom a
  icod_ (Function    a b s t u c d e f g h i j k l m)   = icodeN 1 (\ a b s -> Function a b s t) a b s u c d e f g h i j k l m
  icod_ (Datatype    a b c d e f g h i j)               = icodeN 2 Datatype a b c d e f g h i j
  icod_ (Record      a b c d e f g h i j k l m)         = icodeN 3 Record a b c d e f g h i j k l m
  icod_ (Constructor a b c d e f g h i j k)             = icodeN 4 Constructor a b c d e f g h i j k
  icod_ (Primitive   a b c d e f)                       = icodeN 5 Primitive a b c d e f
  icod_ (PrimitiveSort a b)                             = icodeN 6 PrimitiveSort a b
  icod_ AbstractDefn{}                                  = __IMPOSSIBLE__
  icod_ GeneralizableVar                                = icodeN 7 GeneralizableVar
  icod_ DataOrRecSig{}                                  = __IMPOSSIBLE__

  value = vcase valu where
    valu [0, a]                                        = valuN Axiom a
    valu [1, a, b, s, u, c, d, e, f, g, h, i, j, k, l, m]
                                                       = valuN (\ a b s -> Function a b s Nothing) a b s u c d e f g h i j k l m
    valu [2, a, b, c, d, e, f, g, h, i, j]             = valuN Datatype a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h, i, j, k, l, m]    = valuN Record   a b c d e f g h i j k l m
    valu [4, a, b, c, d, e, f, g, h, i, j, k]          = valuN Constructor a b c d e f g h i j k
    valu [5, a, b, c, d, e, f]                         = valuN Primitive   a b c d e f
    valu [6, a, b]                                     = valuN PrimitiveSort a b
    valu [7]                                           = valuN GeneralizableVar
    valu _                                             = malformed

instance EmbPrj LazySplit where
  icod_ StrictSplit = icodeN' StrictSplit
  icod_ LazySplit   = icodeN 0 LazySplit

  value = vcase valu where
    valu []  = valuN StrictSplit
    valu [0] = valuN LazySplit
    valu _   = malformed

instance EmbPrj SplitTag where
  icod_ (SplitCon c)  = icodeN 0 SplitCon c
  icod_ (SplitLit l)  = icodeN 1 SplitLit l
  icod_ SplitCatchall = icodeN' SplitCatchall

  value = vcase valu where
    valu []     = valuN SplitCatchall
    valu [0, c] = valuN SplitCon c
    valu [1, l] = valuN SplitLit l
    valu _      = malformed

instance EmbPrj a => EmbPrj (SplitTree' a) where
  icod_ (SplittingDone a) = icodeN' SplittingDone a
  icod_ (SplitAt a b c)   = icodeN 0 SplitAt a b c

  value = vcase valu where
    valu [a]          = valuN SplittingDone a
    valu [0, a, b, c] = valuN SplitAt a b c
    valu _            = malformed

instance EmbPrj FunctionFlag where
  icod_ FunStatic       = pure 0
  icod_ FunInline       = pure 1
  icod_ FunMacro        = pure 2

  value = \case
    0 -> pure FunStatic
    1 -> pure FunInline
    2 -> pure FunMacro
    _ -> malformed

instance EmbPrj a => EmbPrj (WithArity a) where
  icod_ (WithArity a b) = icodeN' WithArity a b

  value = valueN WithArity

instance EmbPrj a => EmbPrj (Case a) where
  icod_ (Branches a b c d e f g) = icodeN' Branches a b c d e f g

  value = valueN Branches

-- Opaque blocks are serialised in an abbreviated manner: We only need
-- the enclosed definitions (3rd argument) and parent (4th argument) to
-- compute the transitive closure during scope checking, never
-- afterwards.
instance EmbPrj OpaqueBlock where
  icod_ (OpaqueBlock id uf _ _ r) =
    icodeN' (\id uf ->
      let !unfolding = HashSet.fromList uf
      in OpaqueBlock id unfolding mempty Nothing)
    id (HashSet.toList uf) r

  value = valueN (\id uf -> let !unfolding = HashSet.fromList uf
                            in OpaqueBlock id unfolding mempty Nothing)

instance EmbPrj CompiledClauses where
  icod_ (Fail a)   = icodeN' Fail a
  icod_ (Done a b) = icodeN' Done a (P.killRange b)
  icod_ (Case a b) = icodeN 2 Case a b

  value = vcase valu where
    valu [a]       = valuN Fail a
    valu [a, b]    = valuN Done a b
    valu [2, a, b] = valuN Case a b
    valu _         = malformed

instance EmbPrj a => EmbPrj (FunctionInverse' a) where
  icod_ NotInjective = icodeN' NotInjective
  icod_ (Inverse a)  = icodeN' Inverse a

  value = vcase valu where
    valu []  = valuN NotInjective
    valu [a] = valuN Inverse a
    valu _   = malformed

instance EmbPrj TermHead where
  icod_ SortHead     = icodeN' SortHead
  icod_ PiHead       = icodeN 1 PiHead
  icod_ (ConsHead a) = icodeN 2 ConsHead a
  icod_ (VarHead a)  = icodeN 3 VarHead a
  icod_ UnknownHead  = icodeN 4 UnknownHead

  value = vcase valu where
    valu []     = valuN SortHead
    valu [1]    = valuN PiHead
    valu [2, a] = valuN ConsHead a
    valu [3, a] = valuN VarHead a
    valu [4]    = valuN UnknownHead
    valu _      = malformed

instance EmbPrj I.Clause where
  icod_ (Clause a b c d e f g h i j k l) = icodeN' Clause a b c d e f g h i j k l

  value = valueN Clause

instance EmbPrj I.ConPatternInfo where
  icod_ (ConPatternInfo a b c d e) = icodeN' ConPatternInfo a b c d e

  value = valueN ConPatternInfo

instance EmbPrj I.DBPatVar where
  icod_ (DBPatVar a b) = icodeN' DBPatVar a b

  value = valueN DBPatVar

instance EmbPrj I.PatternInfo where
  icod_ (PatternInfo a b) = icodeN' PatternInfo a b

  value = valueN PatternInfo

instance EmbPrj I.PatOrigin where
  icod_ PatOSystem  = icodeN' PatOSystem
  icod_ PatOSplit   = icodeN 1 PatOSplit
  icod_ (PatOVar a) = icodeN 2 PatOVar a
  icod_ PatODot     = icodeN 3 PatODot
  icod_ PatOWild    = icodeN 4 PatOWild
  icod_ PatOCon     = icodeN 5 PatOCon
  icod_ PatORec     = icodeN 6 PatORec
  icod_ PatOLit     = icodeN 7 PatOLit
  icod_ PatOAbsurd  = icodeN 8 PatOAbsurd

  value = vcase valu where
    valu []     = valuN PatOSystem
    valu [1]    = valuN PatOSplit
    valu [2, a] = valuN PatOVar a
    valu [3]    = valuN PatODot
    valu [4]    = valuN PatOWild
    valu [5]    = valuN PatOCon
    valu [6]    = valuN PatORec
    valu [7]    = valuN PatOLit
    valu [8]    = valuN PatOAbsurd
    valu _      = malformed

instance EmbPrj a => EmbPrj (I.Pattern' a) where
  icod_ (VarP a b  ) = icodeN 0 VarP a b
  icod_ (ConP a b c) = icodeN 1 ConP a b c
  icod_ (LitP a b  ) = icodeN 2 LitP a b
  icod_ (DotP a b  ) = icodeN 3 DotP a b
  icod_ (ProjP a b ) = icodeN 4 ProjP a b
  icod_ (IApplyP a b c d) = icodeN 5 IApplyP a b c d
  icod_ (DefP a b c) = icodeN 6 DefP a b c

  value = vcase valu where
    valu [0, a, b] = valuN VarP a b
    valu [1, a, b, c] = valuN ConP a b c
    valu [2, a, b] = valuN LitP a b
    valu [3, a, b] = valuN DotP a b
    valu [4, a, b] = valuN ProjP a b
    valu [5, a, b, c, d] = valuN IApplyP a b c d
    valu [6, a, b, c] = valuN DefP a b c
    valu _         = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icod_ (Prim    a) = icodeN' Prim a
  icod_ (Builtin a) = icodeN 1 Builtin a
  icod_ (BuiltinRewriteRelations a) = icodeN 2 BuiltinRewriteRelations a

  value = vcase valu where
    valu [a]    = valuN Prim    a
    valu [1, a] = valuN Builtin a
    valu [2, a] = valuN BuiltinRewriteRelations a
    valu _      = malformed

instance EmbPrj a => EmbPrj (Substitution' a) where
  icod_ IdS                = icodeN' IdS
  icod_ (EmptyS a)         = icodeN' EmptyS a
  icod_ (a :# b)           = icodeN' (:#) a b
  icod_ (Strengthen a b c) = icodeN 0 Strengthen a b c
  icod_ (Wk a b)           = icodeN 1 Wk a b
  icod_ (Lift a b)         = icodeN 2 Lift a b

  value = vcase valu where
    valu []           = valuN IdS
    valu [a]          = valuN EmptyS a
    valu [a, b]       = valuN (:#) a b
    valu [0, a, b, c] = valuN Strengthen a b c
    valu [1, a, b]    = valuN Wk a b
    valu [2, a, b]    = valuN Lift a b
    valu _            = malformed

instance EmbPrj Instantiation where
  icod_ (Instantiation a b) = icodeN' Instantiation a b
  value = valueN Instantiation

instance EmbPrj Comparison where
  icod_ CmpEq  = icodeN' CmpEq
  icod_ CmpLeq = icodeN 0 CmpLeq

  value = vcase valu
    where
    valu []  = valuN CmpEq
    valu [0] = valuN CmpLeq
    valu _   = malformed

instance EmbPrj a => EmbPrj (Judgement a) where
  icod_ (HasType a b c) = icodeN' HasType a b c
  icod_ (IsSort a b)    = icodeN' IsSort a b

  value = vcase valu
    where
    valu [a, b, c] = valuN HasType a b c
    valu [a, b]    = valuN IsSort a b
    valu _         = malformed

instance EmbPrj RemoteMetaVariable where
  icod_ (RemoteMetaVariable a b c) = icodeN' RemoteMetaVariable a b c
  value = valueN RemoteMetaVariable
