-- | Extract all names and meta-variables from things.

module Agda.Syntax.Internal.Names where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
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
namesIn' f = namesAndMetasIn' NamesAndMetasInEnv
  { namiEnvSingleQName    = f
  , namiEnvSingleMetaId   = mempty
  , namiEnvSearchInClause = const True
  }

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
metasIn' f = namesAndMetasIn' NamesAndMetasInEnv
  { namiEnvSingleQName    = mempty
  , namiEnvSingleMetaId   = f
  , namiEnvSearchInClause = const True
  }

-- | Some or all of the names and meta-variables that can be found in
-- the given thing.

namesAndMetasIn ::
  (NamesIn a, Collection QName m1, Collection MetaId m2) =>
  a -> (m1, m2)
namesAndMetasIn = namesAndMetasInPartsOf (const True)

-- | A variant of 'namesAndMetasIn' with a predicate that controls the
-- search.

namesAndMetasInPartsOf
  :: (NamesIn a, Collection QName m1, Collection MetaId m2)
  => (Clause -> Bool)  -- ^ Only search in the given clause if the
                       --   predicate returns 'True'.
  -> a -> (m1, m2)
namesAndMetasInPartsOf p = namesAndMetasIn' NamesAndMetasInEnv
  { namiEnvSingleQName    = \x -> (singleton x, mempty)
  , namiEnvSingleMetaId   = \m -> (mempty, singleton m)
  , namiEnvSearchInClause = p
  }

-- | An environment used by 'namesAndMetasIn''.

data NamesAndMetasInEnv m = NamesAndMetasInEnv
  { namiEnvSingleQName :: QName -> m
    -- ^ Records a single 'QName'.
  , namiEnvSingleMetaId :: MetaId -> m
    -- ^ Records a single 'MetaId'.
  , namiEnvSearchInClause :: Clause -> Bool
    -- ^ Only search in the given clause if the
    --   predicate returns 'True'.
  }

class NamesIn a where
  -- | Some or all of the names and meta-variables that can be found
  -- in the given thing.
  namesAndMetasIn' :: Monoid m => NamesAndMetasInEnv m -> a -> m

  default namesAndMetasIn' ::
    (Monoid m, Foldable f, NamesIn b, f b ~ a) =>
    NamesAndMetasInEnv m -> a -> m
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
  namesAndMetasIn' env (Dom _ _ _ t e) =
    mappend (namesAndMetasIn' env t) (namesAndMetasIn' env e)


-- Specific collections
instance NamesIn a => NamesIn (Tele a)

-- Tuples

instance (NamesIn a, NamesIn b) => NamesIn (a, b) where
  namesAndMetasIn' env (x, y) =
    mappend (namesAndMetasIn' env x) (namesAndMetasIn' env y)

instance (NamesIn a, NamesIn b, NamesIn c) => NamesIn (a, b, c) where
  namesAndMetasIn' env (x, y, z) = namesAndMetasIn' env (x, (y, z))

instance (NamesIn a, NamesIn b, NamesIn c, NamesIn d) => NamesIn (a, b, c, d) where
  namesAndMetasIn' env (x, y, z, u) =
    namesAndMetasIn' env ((x, y), (z, u))

instance
  (NamesIn a, NamesIn b, NamesIn c, NamesIn d, NamesIn e) =>
  NamesIn (a, b, c, d, e) where
  namesAndMetasIn' env (x, y, z, u, v) =
    namesAndMetasIn' env ((x, y), (z, (u, v)))

instance
  (NamesIn a, NamesIn b, NamesIn c, NamesIn d, NamesIn e, NamesIn f) =>
  NamesIn (a, b, c, d, e, f) where
  namesAndMetasIn' env (x, y, z, u, v, w) =
    namesAndMetasIn' env ((x, (y, z)), (u, (v, w)))

instance NamesIn CompKit where
  namesAndMetasIn' env (CompKit a b) = namesAndMetasIn' env (a,b)

-- Base cases

instance NamesIn QName where
  namesAndMetasIn' env x = namiEnvSingleQName env x  -- interesting case!

instance NamesIn MetaId where
  namesAndMetasIn' env x = namiEnvSingleMetaId env x

instance NamesIn ConHead where
  namesAndMetasIn' env h = namesAndMetasIn' env (conName h)

instance NamesIn Bool where
  namesAndMetasIn' _ _ = mempty

-- Andreas, 2017-07-27
-- In the following clauses, the choice of fields is not obvious
-- to the reader.  Please comment on the choices.

instance NamesIn Definition where
  namesAndMetasIn' env
    (Defn _ _ t _ _ _ _ disp _ _ _ _ _ _ _ _ _ _ def) =
    namesAndMetasIn' env (t, def, disp)

instance NamesIn Defn where
  namesAndMetasIn' env = \case
    Axiom _            -> mempty
    DataOrRecSig _     -> mempty
    GeneralizableVar   -> mempty
    PrimitiveSort _ s  -> namesAndMetasIn' env s
    AbstractDefn{}     -> __IMPOSSIBLE__
    -- Andreas 2017-07-27, Q: which names can be in @cc@ which are not already in @cl@?
    Function cl cc _ _ _ _ _ _ _ _ _ _ el _ _
      -> namesAndMetasIn' env (cl, cc, el)
    Datatype _ _ cl cs s _ _ _ trX trD
      -> namesAndMetasIn' env (cl, cs, s, trX, trD)
    Record _ cl c _ fs recTel _ _ _ _ _ _ comp
      -> namesAndMetasIn' env (cl, c, fs, recTel, comp)
    Constructor _ _ c d _ _ kit fs _ _
      -> namesAndMetasIn' env (c, d, kit, fs)
    Primitive _ _ cl _ cc
      -> namesAndMetasIn' env (cl, cc)

instance NamesIn Clause where
  namesAndMetasIn' env (Clause _ _ tel ps b t _ _ _ _ _ _) =
    namesAndMetasIn' env (tel, ps, b, t)

instance NamesIn CompiledClauses where
  namesAndMetasIn' env (Case _ c) = namesAndMetasIn' env c
  namesAndMetasIn' env (Done _ v) = namesAndMetasIn' env v
  namesAndMetasIn' env (Fail _)   = mempty

-- Andreas, 2017-07-27
-- Why ignoring the litBranches?
instance NamesIn a => NamesIn (Case a) where
  namesAndMetasIn' env (Branches _ bs _ _ c _ _) =
    namesAndMetasIn' env (bs, c)

instance NamesIn (Pattern' a) where
  namesAndMetasIn' env = \case
    VarP _ _        -> mempty
    LitP _ l        -> namesAndMetasIn' env l
    DotP _ v        -> namesAndMetasIn' env v
    ConP c _ args   -> namesAndMetasIn' env (c, args)
    DefP o q args   -> namesAndMetasIn' env (q, args)
    ProjP _ f       -> namesAndMetasIn' env f
    IApplyP _ t u _ -> namesAndMetasIn' env (t, u)

instance NamesIn a => NamesIn (Type' a) where
  namesAndMetasIn' env (El s t) = namesAndMetasIn' env (s, t)

instance NamesIn Sort where
  namesAndMetasIn' env = \case
    Type l      -> namesAndMetasIn' env l
    Prop l      -> namesAndMetasIn' env l
    Inf _ _     -> mempty
    SSet l      -> namesAndMetasIn' env l
    SizeUniv    -> mempty
    LockUniv    -> mempty
    IntervalUniv -> mempty
    PiSort a b c  -> namesAndMetasIn' env (a, b, c)
    FunSort a b -> namesAndMetasIn' env (a, b)
    UnivSort a  -> namesAndMetasIn' env a
    MetaS x es  -> namesAndMetasIn' env (x, es)
    DefS d es   -> namesAndMetasIn' env (d, es)
    DummyS _    -> mempty

instance NamesIn Term where
  namesAndMetasIn' env = \case
    Var _ args   -> namesAndMetasIn' env args
    Lam _ b      -> namesAndMetasIn' env b
    Lit l        -> namesAndMetasIn' env l
    Def f args   -> namesAndMetasIn' env (f, args)
    Con c _ args -> namesAndMetasIn' env (c, args)
    Pi a b       -> namesAndMetasIn' env (a, b)
    Sort s       -> namesAndMetasIn' env s
    Level l      -> namesAndMetasIn' env l
    MetaV x args -> namesAndMetasIn' env (x, args)
    DontCare v   -> namesAndMetasIn' env v
    Dummy _ args -> namesAndMetasIn' env args

instance NamesIn Level where
  namesAndMetasIn' env (Max _ ls) = namesAndMetasIn' env ls

instance NamesIn PlusLevel where
  namesAndMetasIn' env (Plus _ l) = namesAndMetasIn' env l

-- For QName and Meta literals!
instance NamesIn Literal where
  namesAndMetasIn' env = \case
    LitNat _    -> mempty
    LitWord64 _ -> mempty
    LitString _ -> mempty
    LitChar _   -> mempty
    LitFloat _  -> mempty
    LitQName x  -> namesAndMetasIn' env x
    LitMeta _ m -> namesAndMetasIn' env m

instance NamesIn a => NamesIn (Elim' a) where
  namesAndMetasIn' env (Apply arg)      = namesAndMetasIn' env arg
  namesAndMetasIn' env (Proj _ f)       = namesAndMetasIn' env f
  namesAndMetasIn' env (IApply x y arg) = namesAndMetasIn' env (x, y, arg)

instance NamesIn a => NamesIn (Substitution' a) where
  namesAndMetasIn' env = \case
    IdS              -> mempty
    EmptyS _         -> mempty
    t :# s           -> namesAndMetasIn' env (t, s)
    Strengthen _ _ s -> namesAndMetasIn' env s
    Wk _ s           -> namesAndMetasIn' env s
    Lift _ s         -> namesAndMetasIn' env s

instance NamesIn DisplayForm where
  namesAndMetasIn' env (Display _ ps v) = namesAndMetasIn' env (ps, v)

instance NamesIn DisplayTerm where
  namesAndMetasIn' env = \case
    DWithApp v us es -> namesAndMetasIn' env (v, us, es)
    DCon c _ vs      -> namesAndMetasIn' env (c, vs)
    DDef f es        -> namesAndMetasIn' env (f, es)
    DDot v           -> namesAndMetasIn' env v
    DTerm v          -> namesAndMetasIn' env v

instance NamesIn a => NamesIn (Builtin a) where
  namesAndMetasIn' env = \case
    Builtin t -> namesAndMetasIn' env t
    Prim x    -> namesAndMetasIn' env x
    BuiltinRewriteRelations xs -> namesAndMetasIn' env xs

-- | Note that the 'primFunImplementation' is skipped.
instance NamesIn PrimFun where
  namesAndMetasIn' env = \case
    PrimFun x _ _ -> namesAndMetasIn' env x

instance NamesIn Section where
  namesAndMetasIn' env = \case
    Section tel -> namesAndMetasIn' env tel

instance NamesIn NLPat where
  namesAndMetasIn' env = \case
    PVar _ _      -> mempty
    PDef a b      -> namesAndMetasIn' env (a, b)
    PLam _ a      -> namesAndMetasIn' env a
    PPi a b       -> namesAndMetasIn' env (a, b)
    PSort a       -> namesAndMetasIn' env a
    PBoundVar _ a -> namesAndMetasIn' env a
    PTerm a       -> namesAndMetasIn' env a

instance NamesIn NLPType where
  namesAndMetasIn' env = \case
    NLPType a b -> namesAndMetasIn' env (a, b)

instance NamesIn NLPSort where
  namesAndMetasIn' env = \case
    PType a       -> namesAndMetasIn' env a
    PProp a       -> namesAndMetasIn' env a
    PSSet a       -> namesAndMetasIn' env a
    PInf _ _      -> mempty
    PSizeUniv     -> mempty
    PLockUniv     -> mempty
    PIntervalUniv -> mempty

instance NamesIn RewriteRule where
  namesAndMetasIn' env = \case
    RewriteRule a b c d e f _ ->
      namesAndMetasIn' env (a, b, c, d, e, f)

instance (NamesIn a, NamesIn b) => NamesIn (HashMap a b) where
  namesAndMetasIn' env = namesAndMetasIn' env . HMap.toList

instance NamesIn System where
  namesAndMetasIn' env (System tel cs) = namesAndMetasIn' env (tel, cs)

instance NamesIn ExtLamInfo where
  namesAndMetasIn' env (ExtLamInfo _ _ s) = namesAndMetasIn' env s

instance NamesIn a => NamesIn (FunctionInverse' a) where
  namesAndMetasIn' env = \case
    NotInjective -> mempty
    Inverse m  -> namesAndMetasIn' env m

instance NamesIn TTerm where
  namesAndMetasIn' env = \case
    TVar _         -> mempty
    TPrim _        -> mempty
    TDef x         -> namesAndMetasIn' env x
    TApp t xs      -> namesAndMetasIn' env (t, xs)
    TLam t         -> namesAndMetasIn' env t
    TLit l         -> namesAndMetasIn' env l
    TCon x         -> namesAndMetasIn' env x
    TLet t1 t2     -> namesAndMetasIn' env (t1, t2)
    TCase _ c t ts -> namesAndMetasIn' env (c, t, ts)
    TUnit          -> mempty
    TSort          -> mempty
    TErased        -> mempty
    TCoerce t      -> namesAndMetasIn' env t
    TError _       -> mempty

instance NamesIn TAlt where
  namesAndMetasIn' env = \case
    TACon x _ t   -> namesAndMetasIn' env (x, t)
    TAGuard t1 t2 -> namesAndMetasIn' env (t1, t2)
    TALit l t     -> namesAndMetasIn' env (l, t)

instance NamesIn CaseType where
  namesAndMetasIn' env = \case
    CTData _ x -> namesAndMetasIn' env x
    CTNat      -> mempty
    CTInt      -> mempty
    CTChar     -> mempty
    CTString   -> mempty
    CTFloat    -> mempty
    CTQName    -> mempty

instance NamesIn CaseInfo where
  namesAndMetasIn' env (CaseInfo _ t) = namesAndMetasIn' env t

instance NamesIn Compiled where
  namesAndMetasIn' env (Compiled t _) = namesAndMetasIn' env t

-- Pattern synonym stuff --

newtype PSyn = PSyn A.PatternSynDefn
instance NamesIn PSyn where
  namesAndMetasIn' env (PSyn (_args, p)) = namesAndMetasIn' env p

instance NamesIn (A.Pattern' a) where
  namesAndMetasIn' env = \case
    A.VarP _               -> mempty
    A.ConP _ c args        -> namesAndMetasIn' env (c, args)
    A.ProjP _ _ d          -> namesAndMetasIn' env d
    A.DefP _ f args        -> namesAndMetasIn' env (f, args)
    A.WildP _              -> mempty
    A.AsP _ _ p            -> namesAndMetasIn' env p
    A.AbsurdP _            -> mempty
    A.LitP _ l             -> namesAndMetasIn' env l
    A.PatternSynP _ c args -> namesAndMetasIn' env (c, args)
    A.RecP _ fs            -> namesAndMetasIn' env fs
    A.DotP{}               -> __IMPOSSIBLE__    -- Dot patterns are not allowed in pattern synonyms
    A.EqualP{}             -> __IMPOSSIBLE__    -- Andrea: should we allow these in pattern synonyms?
    A.WithP _ p            -> namesAndMetasIn' env p
    A.AnnP _ a p           -> __IMPOSSIBLE__    -- Type annotations are not (yet) allowed in pattern synonyms

instance NamesIn AmbiguousQName where
  namesAndMetasIn' env (AmbQ cs) = namesAndMetasIn' env cs
