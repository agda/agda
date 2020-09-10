{-# LANGUAGE TypeFamilies #-}

-- | Extract all names from things.

module Agda.Syntax.Internal.Names where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Set (Set)

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause

import Agda.Utils.Singleton
import Agda.Utils.Impossible

namesIn :: (NamesIn a, Collection QName m) => a -> m
namesIn = namesIn' singleton

class NamesIn a where
  namesIn' :: Monoid m => (QName -> m) -> a -> m

  default namesIn' :: (Monoid m, Foldable f, NamesIn b, f b ~ a) => (QName -> m) -> a -> m
  namesIn' = foldMap . namesIn'

-- Generic collections
instance NamesIn a => NamesIn (Maybe a)
instance NamesIn a => NamesIn [a]
instance NamesIn a => NamesIn (NonEmpty a)
instance NamesIn a => NamesIn (Set a)
instance NamesIn a => NamesIn (Map k a)

-- Decorations
instance NamesIn a => NamesIn (Arg a)
instance NamesIn a => NamesIn (Dom a)
instance NamesIn a => NamesIn (Named n a)
instance NamesIn a => NamesIn (Abs a)
instance NamesIn a => NamesIn (WithArity a)
instance NamesIn a => NamesIn (Open a)
instance NamesIn a => NamesIn (C.FieldAssignment' a)

-- Specific collections
instance NamesIn a => NamesIn (Tele a)

-- Tuples

instance (NamesIn a, NamesIn b) => NamesIn (a, b) where
  namesIn' sg (x, y) = mappend (namesIn' sg x) (namesIn' sg y)

instance (NamesIn a, NamesIn b, NamesIn c) => NamesIn (a, b, c) where
  namesIn' sg (x, y, z) = namesIn' sg (x, (y, z))

instance (NamesIn a, NamesIn b, NamesIn c, NamesIn d) => NamesIn (a, b, c, d) where
  namesIn' sg (x, y, z, u) = namesIn' sg ((x, y), (z, u))

instance NamesIn CompKit where
  namesIn' sg (CompKit a b) = namesIn' sg (a,b)

-- Base case

instance NamesIn QName where
  namesIn' sg x = sg x  -- interesting case!

instance NamesIn ConHead where
  namesIn' sg h = namesIn' sg (conName h)

-- Andreas, 2017-07-27
-- In the following clauses, the choice of fields is not obvious
-- to the reader.  Please comment on the choices.
--
-- Also, this would be more robust if these were constructor-style
-- matches instead of record-style matches.
-- If someone adds a field containing names, this would go unnoticed.

instance NamesIn Definition where
  namesIn' sg def = namesIn' sg (defType def, theDef def, defDisplay def)

instance NamesIn Defn where
  namesIn' sg = \case
    Axiom              -> mempty
    DataOrRecSig{}     -> mempty
    GeneralizableVar{} -> mempty
    PrimitiveSort{}    -> mempty
    AbstractDefn{}     -> __IMPOSSIBLE__
    -- Andreas 2017-07-27, Q: which names can be in @cc@ which are not already in @cl@?
    Function    { funClauses = cl, funCompiled = cc }
      -> namesIn' sg (cl, cc)
    Datatype    { dataClause = cl, dataCons = cs, dataSort = s }
      -> namesIn' sg (cl, cs, s)
    Record      { recClause = cl, recConHead = c, recFields = fs, recComp = comp }
      -> namesIn' sg (cl, c, fs, comp)
      -- Don't need recTel since those will be reachable from the constructor
    Constructor { conSrcCon = c, conData = d, conComp = kit, conProj = fs }
      -> namesIn' sg (c, d, kit, fs)
    Primitive   { primClauses = cl, primCompiled = cc }
      -> namesIn' sg (cl, cc)

instance NamesIn Clause where
  namesIn' sg Clause{ clauseTel = tel, namedClausePats = ps, clauseBody = b, clauseType = t } =
    namesIn' sg (tel, ps, b, t)

instance NamesIn CompiledClauses where
  namesIn' sg (Case _ c) = namesIn' sg c
  namesIn' sg (Done _ v) = namesIn' sg v
  namesIn' sg Fail       = mempty

-- Andreas, 2017-07-27
-- Why ignoring the litBranches?
instance NamesIn a => NamesIn (Case a) where
  namesIn' sg Branches{ conBranches = bs, catchAllBranch = c } =
    namesIn' sg (bs, c)

instance NamesIn (Pattern' a) where
  namesIn' sg = \case
    VarP{}          -> mempty
    LitP _ l        -> namesIn' sg l
    DotP _ v        -> namesIn' sg v
    ConP c _ args   -> namesIn' sg (c, args)
    DefP o q args   -> namesIn' sg (q, args)
    ProjP _ f       -> namesIn' sg f
    IApplyP _ t u _ -> namesIn' sg (t, u)

instance NamesIn a => NamesIn (Type' a) where
  namesIn' sg (El s t) = namesIn' sg (s, t)

instance NamesIn Sort where
  namesIn' sg = \case
    Type l      -> namesIn' sg l
    Prop l      -> namesIn' sg l
    Inf _ _     -> mempty
    SSet l      -> namesIn' sg l
    SizeUniv    -> mempty
    LockUniv    -> mempty
    PiSort a b  -> namesIn' sg (a, b)
    FunSort a b -> namesIn' sg (a, b)
    UnivSort a  -> namesIn' sg a
    MetaS _ es  -> namesIn' sg es
    DefS d es   -> namesIn' sg (d, es)
    DummyS{}    -> mempty

instance NamesIn Term where
  namesIn' sg = \case
    Var _ args   -> namesIn' sg args
    Lam _ b      -> namesIn' sg b
    Lit l        -> namesIn' sg l
    Def f args   -> namesIn' sg (f, args)
    Con c _ args -> namesIn' sg (c, args)
    Pi a b       -> namesIn' sg (a, b)
    Sort s       -> namesIn' sg s
    Level l      -> namesIn' sg l
    MetaV _ args -> namesIn' sg args
    DontCare v   -> namesIn' sg v
    Dummy{}      -> mempty

instance NamesIn Level where
  namesIn' sg (Max _ ls) = namesIn' sg ls

instance NamesIn PlusLevel where
  namesIn' sg (Plus _ l) = namesIn' sg l

-- For QName literals!
instance NamesIn Literal where
  namesIn' sg = \case
    LitNat{}      -> mempty
    LitWord64{}   -> mempty
    LitString{}   -> mempty
    LitChar{}     -> mempty
    LitFloat{}    -> mempty
    LitQName    x -> namesIn' sg x
    LitMeta{}     -> mempty

instance NamesIn a => NamesIn (Elim' a) where
  namesIn' sg (Apply arg)      = namesIn' sg arg
  namesIn' sg (Proj _ f)       = namesIn' sg f
  namesIn' sg (IApply x y arg) = namesIn' sg (x, y, arg)

instance NamesIn DisplayForm where
  namesIn' sg (Display _ ps v) = namesIn' sg (ps, v)

instance NamesIn DisplayTerm where
  namesIn' sg = \case
    DWithApp v us es -> namesIn' sg (v, us, es)
    DCon c _ vs      -> namesIn' sg (c, vs)
    DDef f es        -> namesIn' sg (f, es)
    DDot v           -> namesIn' sg v
    DTerm v          -> namesIn' sg v

-- Pattern synonym stuff --

newtype PSyn = PSyn A.PatternSynDefn
instance NamesIn PSyn where
  namesIn' sg (PSyn (_args, p)) = namesIn' sg p

instance NamesIn (A.Pattern' a) where
  namesIn' sg = \case
    A.VarP{}               -> mempty
    A.ConP _ c args        -> namesIn' sg (c, args)
    A.ProjP _ _ d          -> namesIn' sg d
    A.DefP _ f args        -> namesIn' sg (f, args)
    A.WildP{}              -> mempty
    A.AsP _ _ p            -> namesIn' sg p
    A.AbsurdP{}            -> mempty
    A.LitP _ l             -> namesIn' sg l
    A.PatternSynP _ c args -> namesIn' sg (c, args)
    A.RecP _ fs            -> namesIn' sg fs
    A.DotP{}               -> __IMPOSSIBLE__    -- Dot patterns are not allowed in pattern synonyms
    A.EqualP{}             -> __IMPOSSIBLE__    -- Andrea: should we allow these in pattern synonyms?
    A.WithP _ p            -> namesIn' sg p

instance NamesIn AmbiguousQName where
  namesIn' sg (AmbQ cs) = namesIn' sg cs
