{-# OPTIONS_GHC -Wunused-imports #-}

-- | Extract all names and meta-variables from things.

module Agda.Syntax.Internal.Names where

import Data.HashMap.Strict (HashMap)
import Data.Map (Map)
import Data.Set (Set)

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause

import Agda.Utils.List1 (List1)
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Singleton
import Agda.Utils.Impossible

-- | Some or all of the 'QName's that can be found in the given thing.

namesIn :: (NamesIn a, Collection QName m) => a -> m
namesIn = namesIn' singleton

-- | Some or all of the 'QName's that can be found in the given thing.

namesIn' :: (NamesIn a, Monoid m) => (QName -> m) -> a -> m
namesIn' f = namesAndMetasIn' (either f mempty)

-- | Some or all of the meta-variables that can be found in the given
-- thing.

metasIn :: (NamesIn a, Collection MetaId m) => a -> m
metasIn = metasIn' singleton

-- | Some or all of the meta-variables that can be found in the given
-- thing.

-- TODO: Does this function make
-- Agda.Syntax.Internal.MetaVars.allMetas superfluous? Maybe not,
-- allMetas ignores the first argument of PiSort.

metasIn' :: (NamesIn a, Monoid m) => (MetaId -> m) -> a -> m
metasIn' f = namesAndMetasIn' (either mempty f)

-- | Some or all of the names and meta-variables that can be found in
-- the given thing.

namesAndMetasIn ::
  (NamesIn a, Collection QName m1, Collection MetaId m2) =>
  a -> (m1, m2)
namesAndMetasIn =
  namesAndMetasIn'
    (either (\x -> (singleton x, mempty))
            (\m -> (mempty, singleton m)))

class NamesIn a where
  -- | Some or all of the names and meta-variables that can be found
  -- in the given thing.
  namesAndMetasIn' :: Monoid m => (Either QName MetaId -> m) -> a -> m

  default namesAndMetasIn' ::
    (Monoid m, Foldable f, NamesIn b, f b ~ a) =>
    (Either QName MetaId -> m) -> a -> m
  namesAndMetasIn' = foldMap . namesAndMetasIn'

-- Generic collections
instance NamesIn a => NamesIn (Maybe a)
instance NamesIn a => NamesIn (Strict.Maybe a)
instance NamesIn a => NamesIn [a]
instance NamesIn a => NamesIn (List1 a)
instance NamesIn a => NamesIn (Set a)
instance NamesIn a => NamesIn (Map k a)

-- Decorations
instance NamesIn a => NamesIn (Arg a)
instance NamesIn a => NamesIn (Named n a)
instance NamesIn a => NamesIn (Abs a)
instance NamesIn a => NamesIn (WithArity a)
instance NamesIn a => NamesIn (Open a)
instance NamesIn a => NamesIn (C.FieldAssignment' a)

instance (NamesIn a, NamesIn b) => NamesIn (Dom' a b) where
  namesAndMetasIn' sg (Dom _ _ _ t e) =
    mappend (namesAndMetasIn' sg t) (namesAndMetasIn' sg e)


-- Specific collections
instance NamesIn a => NamesIn (Tele a)

-- Tuples

instance (NamesIn a, NamesIn b) => NamesIn (a, b) where
  namesAndMetasIn' sg (x, y) =
    namesAndMetasIn' sg x <> namesAndMetasIn' sg y
  {-# INLINE namesAndMetasIn' #-}

instance (NamesIn a, NamesIn b, NamesIn c) => NamesIn (a, b, c) where
  namesAndMetasIn' sg (x, y, z) =
    namesAndMetasIn' sg x <> namesAndMetasIn' sg y <> namesAndMetasIn' sg z
  {-# INLINE namesAndMetasIn' #-}

instance (NamesIn a, NamesIn b, NamesIn c, NamesIn d) => NamesIn (a, b, c, d) where
  namesAndMetasIn' sg (x, y, z, u) =
    namesAndMetasIn' sg x <> namesAndMetasIn' sg y <> namesAndMetasIn' sg z <> namesAndMetasIn' sg u
  {-# INLINE namesAndMetasIn' #-}

instance
  (NamesIn a, NamesIn b, NamesIn c, NamesIn d, NamesIn e) =>
  NamesIn (a, b, c, d, e) where
  namesAndMetasIn' sg (x, y, z, u, v) =
    namesAndMetasIn' sg x <> namesAndMetasIn' sg y <> namesAndMetasIn' sg z <> namesAndMetasIn' sg u
    <> namesAndMetasIn' sg v
  {-# INLINE namesAndMetasIn' #-}

instance
  (NamesIn a, NamesIn b, NamesIn c, NamesIn d, NamesIn e, NamesIn f) =>
  NamesIn (a, b, c, d, e, f) where
  namesAndMetasIn' sg (x, y, z, u, v, w) =
    namesAndMetasIn' sg x <> namesAndMetasIn' sg y <> namesAndMetasIn' sg z <> namesAndMetasIn' sg u
    <> namesAndMetasIn' sg v <> namesAndMetasIn' sg w
  {-# INLINE namesAndMetasIn' #-}

instance NamesIn CompKit where
  namesAndMetasIn' sg (CompKit a b) = namesAndMetasIn' sg (a,b)

-- Base cases

instance NamesIn QName where
  namesAndMetasIn' sg x = sg (Left x)  -- interesting case!

instance NamesIn MetaId where
  namesAndMetasIn' sg x = sg (Right x)

instance NamesIn ConHead where
  namesAndMetasIn' sg h = namesAndMetasIn' sg (conName h)

instance NamesIn Bool where
  namesAndMetasIn' _ _ = mempty

-- Andreas, 2017-07-27
-- In the following clauses, the choice of fields is not obvious
-- to the reader.  Please comment on the choices.

instance NamesIn Definition where
  namesAndMetasIn' sg
    (Defn _ _ t _ _ _ _ _ disp _ _ _ _ _ _ _ _ _ _ def) =
    namesAndMetasIn' sg (t, def, disp)

instance NamesIn Defn where
  namesAndMetasIn' sg = \case
    Axiom _            -> mempty
    DataOrRecSig _     -> mempty
    GeneralizableVar   -> mempty
    PrimitiveSort _ s  -> namesAndMetasIn' sg s
    AbstractDefn{}     -> __IMPOSSIBLE__
    -- Andreas 2017-07-27, Q: which names can be in @cc@ which are not already in @cl@?
    Function cl cc _ _ _ _ _ _ _ _ _ _ el _ _ _
      -> namesAndMetasIn' sg (cl, cc, el)
    Datatype _ _ cl cs s _ _ _ trX trD
      -> namesAndMetasIn' sg (cl, cs, s, trX, trD)
    Record _ cl c _ fs recTel _ _ _ _ _ _ comp
      -> namesAndMetasIn' sg (cl, c, fs, recTel, comp)
    Constructor _ _ c d _ kit fs _ _ _ _
      -> namesAndMetasIn' sg (c, d, kit, fs)
    Primitive _ _ cl _ cc _
      -> namesAndMetasIn' sg (cl, cc)

instance NamesIn Clause where
  namesAndMetasIn' sg (Clause _ _ tel ps b t _ _ _ _ _ _) =
    namesAndMetasIn' sg (tel, ps, b, t)

instance NamesIn CompiledClauses where
  namesAndMetasIn' sg (Case _ c) = namesAndMetasIn' sg c
  namesAndMetasIn' sg (Done _ v) = namesAndMetasIn' sg v
  namesAndMetasIn' sg (Fail _)   = mempty

-- Andreas, 2017-07-27
-- Why ignoring the litBranches?
instance NamesIn a => NamesIn (Case a) where
  namesAndMetasIn' sg (Branches _ bs _ _ c _ _) =
    namesAndMetasIn' sg (bs, c)

instance NamesIn (Pattern' a) where
  namesAndMetasIn' sg = \case
    VarP _ _        -> mempty
    LitP _ l        -> namesAndMetasIn' sg l
    DotP _ v        -> namesAndMetasIn' sg v
    ConP c _ args   -> namesAndMetasIn' sg (c, args)
    DefP o q args   -> namesAndMetasIn' sg (q, args)
    ProjP _ f       -> namesAndMetasIn' sg f
    IApplyP _ t u _ -> namesAndMetasIn' sg (t, u)

instance NamesIn a => NamesIn (Type' a) where
  namesAndMetasIn' sg (El s t) = namesAndMetasIn' sg (s, t)

instance NamesIn Sort where
  namesAndMetasIn' sg = \case
    Univ _ l    -> namesAndMetasIn' sg l
    Inf _ _     -> mempty
    SizeUniv    -> mempty
    LockUniv    -> mempty
    LevelUniv   -> mempty
    IntervalUniv -> mempty
    PiSort a b c  -> namesAndMetasIn' sg (a, b, c)
    FunSort a b -> namesAndMetasIn' sg (a, b)
    UnivSort a  -> namesAndMetasIn' sg a
    MetaS x es  -> namesAndMetasIn' sg (x, es)
    DefS d es   -> namesAndMetasIn' sg (d, es)
    DummyS _    -> mempty

instance NamesIn Term where
  namesAndMetasIn' sg = \case
    Var _ args   -> namesAndMetasIn' sg args
    Lam _ b      -> namesAndMetasIn' sg b
    Lit l        -> namesAndMetasIn' sg l
    Def f args   -> namesAndMetasIn' sg (f, args)
    Con c _ args -> namesAndMetasIn' sg (c, args)
    Pi a b       -> namesAndMetasIn' sg (a, b)
    Sort s       -> namesAndMetasIn' sg s
    Level l      -> namesAndMetasIn' sg l
    MetaV x args -> namesAndMetasIn' sg (x, args)
    DontCare v   -> namesAndMetasIn' sg v
    Dummy _ args -> namesAndMetasIn' sg args

instance NamesIn Level where
  namesAndMetasIn' sg (Max _ ls) = namesAndMetasIn' sg ls

instance NamesIn PlusLevel where
  namesAndMetasIn' sg (Plus _ l) = namesAndMetasIn' sg l

-- For QName and Meta literals!
instance NamesIn Literal where
  namesAndMetasIn' sg = \case
    LitNat _    -> mempty
    LitWord64 _ -> mempty
    LitString _ -> mempty
    LitChar _   -> mempty
    LitFloat _  -> mempty
    LitQName x  -> namesAndMetasIn' sg x
    LitMeta _ m -> namesAndMetasIn' sg m

instance NamesIn a => NamesIn (Elim' a) where
  namesAndMetasIn' sg (Apply arg)      = namesAndMetasIn' sg arg
  namesAndMetasIn' sg (Proj _ f)       = namesAndMetasIn' sg f
  namesAndMetasIn' sg (IApply x y arg) = namesAndMetasIn' sg (x, y, arg)

instance NamesIn a => NamesIn (Substitution' a) where
  namesAndMetasIn' sg = \case
    IdS              -> mempty
    EmptyS _         -> mempty
    t :# s           -> namesAndMetasIn' sg (t, s)
    Strengthen _ _ s -> namesAndMetasIn' sg s
    Wk _ s           -> namesAndMetasIn' sg s
    Lift _ s         -> namesAndMetasIn' sg s

instance NamesIn DisplayForm where
  namesAndMetasIn' sg (Display _ ps v) = namesAndMetasIn' sg (ps, v)

instance NamesIn DisplayTerm where
  namesAndMetasIn' sg = \case
    DWithApp v us es -> namesAndMetasIn' sg (v, us, es)
    DCon c _ vs      -> namesAndMetasIn' sg (c, vs)
    DDef f es        -> namesAndMetasIn' sg (f, es)
    DDot' v es       -> namesAndMetasIn' sg (v, es)
    DTerm' v es      -> namesAndMetasIn' sg (v, es)

instance NamesIn a => NamesIn (Builtin a) where
  namesAndMetasIn' sg = \case
    Builtin t -> namesAndMetasIn' sg t
    Prim x    -> namesAndMetasIn' sg x
    BuiltinRewriteRelations xs -> namesAndMetasIn' sg xs

-- | Note that the 'primFunImplementation' is skipped.
instance NamesIn PrimFun where
  namesAndMetasIn' sg = \case
    PrimFun x _ _ _ -> namesAndMetasIn' sg x

instance NamesIn Section where
  namesAndMetasIn' sg = \case
    Section tel -> namesAndMetasIn' sg tel

instance NamesIn NLPat where
  namesAndMetasIn' sg = \case
    PVar _ _      -> mempty
    PDef a b      -> namesAndMetasIn' sg (a, b)
    PLam _ a      -> namesAndMetasIn' sg a
    PPi a b       -> namesAndMetasIn' sg (a, b)
    PSort a       -> namesAndMetasIn' sg a
    PBoundVar _ a -> namesAndMetasIn' sg a
    PTerm a       -> namesAndMetasIn' sg a

instance NamesIn NLPType where
  namesAndMetasIn' sg = \case
    NLPType a b -> namesAndMetasIn' sg (a, b)

instance NamesIn NLPSort where
  namesAndMetasIn' sg = \case
    PUniv _ a     -> namesAndMetasIn' sg a
    PInf _ _      -> mempty
    PSizeUniv     -> mempty
    PLockUniv     -> mempty
    PLevelUniv    -> mempty
    PIntervalUniv -> mempty

instance NamesIn RewriteRule where
  namesAndMetasIn' sg = \case
    RewriteRule a b c d e f _ ->
      namesAndMetasIn' sg (a, b, c, d, e, f)

instance (NamesIn a, NamesIn b) => NamesIn (HashMap a b) where
  namesAndMetasIn' sg map = foldMap (namesAndMetasIn' sg) map

instance NamesIn System where
  namesAndMetasIn' sg (System tel cs) = namesAndMetasIn' sg (tel, cs)

instance NamesIn ExtLamInfo where
  namesAndMetasIn' sg (ExtLamInfo _ _ s) = namesAndMetasIn' sg s

instance NamesIn a => NamesIn (FunctionInverse' a) where
  namesAndMetasIn' sg = \case
    NotInjective -> mempty
    Inverse m  -> namesAndMetasIn' sg m

instance NamesIn TTerm where
  namesAndMetasIn' sg = \case
    TVar _         -> mempty
    TPrim _        -> mempty
    TDef x         -> namesAndMetasIn' sg x
    TApp t xs      -> namesAndMetasIn' sg (t, xs)
    TLam t         -> namesAndMetasIn' sg t
    TLit l         -> namesAndMetasIn' sg l
    TCon x         -> namesAndMetasIn' sg x
    TLet t1 t2     -> namesAndMetasIn' sg (t1, t2)
    TCase _ c t ts -> namesAndMetasIn' sg (c, t, ts)
    TUnit          -> mempty
    TSort          -> mempty
    TErased        -> mempty
    TCoerce t      -> namesAndMetasIn' sg t
    TError _       -> mempty

instance NamesIn TAlt where
  namesAndMetasIn' sg = \case
    TACon x _ t   -> namesAndMetasIn' sg (x, t)
    TAGuard t1 t2 -> namesAndMetasIn' sg (t1, t2)
    TALit l t     -> namesAndMetasIn' sg (l, t)

instance NamesIn CaseType where
  namesAndMetasIn' sg = \case
    CTData x   -> namesAndMetasIn' sg x
    CTNat      -> mempty
    CTInt      -> mempty
    CTChar     -> mempty
    CTString   -> mempty
    CTFloat    -> mempty
    CTQName    -> mempty

instance NamesIn CaseInfo where
  namesAndMetasIn' sg (CaseInfo _ _ t) = namesAndMetasIn' sg t

instance NamesIn Compiled where
  namesAndMetasIn' sg (Compiled t _) = namesAndMetasIn' sg t

-- Pattern synonym stuff --

newtype PSyn = PSyn A.PatternSynDefn
instance NamesIn PSyn where
  namesAndMetasIn' sg (PSyn (_args, p)) = namesAndMetasIn' sg p

instance NamesIn (A.Pattern' a) where
  namesAndMetasIn' sg = \case
    A.VarP _               -> mempty
    A.ConP _ c args        -> namesAndMetasIn' sg (c, args)
    A.ProjP _ _ d          -> namesAndMetasIn' sg d
    A.DefP _ f args        -> namesAndMetasIn' sg (f, args)
    A.WildP _              -> mempty
    A.AsP _ _ p            -> namesAndMetasIn' sg p
    A.AbsurdP _            -> mempty
    A.LitP _ l             -> namesAndMetasIn' sg l
    A.PatternSynP _ c args -> namesAndMetasIn' sg (c, args)
    A.RecP _ fs            -> namesAndMetasIn' sg fs
    A.DotP{}               -> __IMPOSSIBLE__    -- Dot patterns are not allowed in pattern synonyms
    A.EqualP{}             -> __IMPOSSIBLE__    -- Andrea: should we allow these in pattern synonyms?
    A.WithP _ p            -> namesAndMetasIn' sg p
    A.AnnP _ a p           -> __IMPOSSIBLE__    -- Type annotations are not (yet) allowed in pattern synonyms

instance NamesIn AmbiguousQName where
  namesAndMetasIn' sg (AmbQ cs) = namesAndMetasIn' sg cs
