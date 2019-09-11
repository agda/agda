{-# LANGUAGE TypeFamilies #-}

-- | Extract all names from things.

module Agda.Syntax.Internal.Names where

import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause

import Agda.Utils.NonemptyList

import Agda.Utils.Impossible

class NamesIn a where
  namesIn :: a -> Set QName

  default namesIn :: (Foldable f, NamesIn b, f b ~ a) => a -> Set QName
  namesIn = foldMap namesIn

instance NamesIn a => NamesIn (Maybe a)              where
instance NamesIn a => NamesIn [a]                    where
instance NamesIn a => NamesIn (NonemptyList a)       where
instance NamesIn a => NamesIn (Arg a)                where
instance NamesIn a => NamesIn (Dom a)                where
instance NamesIn a => NamesIn (Named n a)            where
instance NamesIn a => NamesIn (Abs a)                where
instance NamesIn a => NamesIn (WithArity a)          where
instance NamesIn a => NamesIn (Tele a)               where
instance NamesIn a => NamesIn (C.FieldAssignment' a) where

instance NamesIn Void where
  namesIn _ = Set.empty

instance (NamesIn a, NamesIn b) => NamesIn (a, b) where
  namesIn (x, y) = Set.union (namesIn x) (namesIn y)

instance (NamesIn a, NamesIn b, NamesIn c) => NamesIn (a, b, c) where
  namesIn (x, y, z) = namesIn (x, (y, z))

instance (NamesIn a, NamesIn b, NamesIn c, NamesIn d) => NamesIn (a, b, c, d) where
  namesIn (x, y, z, u) = namesIn ((x, y), (z, u))

instance NamesIn CompKit where
  namesIn (CompKit a b) = namesIn (a,b)

-- Andreas, 2017-07-27
-- In the following clauses, the choice of fields is not obvious
-- to the reader.  Please comment on the choices.
--
-- Also, this would be more robust if these were constructor-style
-- matches instead of record-style matches.
-- If someone adds a field containing names, this would go unnoticed.

instance NamesIn Definition where
  namesIn def = namesIn (defType def, theDef def, defDisplay def)

instance NamesIn Defn where
  namesIn def = case def of
    Axiom -> Set.empty
    DataOrRecSig{} -> Set.empty
    GeneralizableVar{} -> Set.empty
    -- Andreas 2017-07-27, Q: which names can be in @cc@ which are not already in @cl@?
    Function    { funClauses = cl, funCompiled = cc }              -> namesIn (cl, cc)
    Datatype    { dataClause = cl, dataCons = cs, dataSort = s }   -> namesIn (cl, cs, s)
    Record      { recClause = cl, recConHead = c, recFields = fs, recComp = comp } -> namesIn (cl, c, fs, comp)
      -- Don't need recTel since those will be reachable from the constructor
    Constructor { conSrcCon = c, conData = d, conComp = kit, conProj = fs }        -> namesIn (c, d, kit, fs)
    Primitive   { primClauses = cl, primCompiled = cc }            -> namesIn (cl, cc)
    AbstractDefn{} -> __IMPOSSIBLE__

instance NamesIn Clause where
  namesIn Clause{ clauseTel = tel, namedClausePats = ps, clauseBody = b, clauseType = t } =
    namesIn (tel, ps, b, t)

instance NamesIn CompiledClauses where
  namesIn (Case _ c) = namesIn c
  namesIn (Done _ v) = namesIn v
  namesIn Fail       = Set.empty

-- Andreas, 2017-07-27
-- Why ignoring the litBranches?
instance NamesIn a => NamesIn (Case a) where
  namesIn Branches{ conBranches = bs, catchAllBranch = c } =
    namesIn (Map.toList bs, c)

instance NamesIn (Pattern' a) where
  namesIn p = case p of
    VarP{}        -> Set.empty
    LitP l        -> namesIn l
    DotP _ v      -> namesIn v
    ConP c _ args -> namesIn (c, args)
    DefP o q args -> namesIn (q, args)
    ProjP _ f     -> namesIn f
    IApplyP _ t u _ -> namesIn (t, u)

instance NamesIn a => NamesIn (Type' a) where
  namesIn (El s t) = namesIn (s, t)

instance NamesIn Sort where
  namesIn s = case s of
    Type l   -> namesIn l
    Prop l   -> namesIn l
    Inf      -> Set.empty
    SizeUniv -> Set.empty
    PiSort a b -> namesIn (a, b)
    UnivSort a -> namesIn a
    MetaS _ es -> namesIn es
    DefS d es  -> namesIn (d, es)
    DummyS{}   -> Set.empty

instance NamesIn Term where
  namesIn v = case v of
    Var _ args   -> namesIn args
    Lam _ b      -> namesIn b
    Lit l        -> namesIn l
    Def f args   -> namesIn (f, args)
    Con c _ args -> namesIn (c, args)
    Pi a b       -> namesIn (a, b)
    Sort s       -> namesIn s
    Level l      -> namesIn l
    MetaV _ args -> namesIn args
    DontCare v   -> namesIn v
    Dummy{}      -> Set.empty

instance NamesIn Level where
  namesIn (Max ls) = namesIn ls

instance NamesIn PlusLevel where
  namesIn ClosedLevel{} = Set.empty
  namesIn (Plus _ l)    = namesIn l

instance NamesIn LevelAtom where
  namesIn l = case l of
    MetaLevel _ args -> namesIn args
    BlockedLevel _ v -> namesIn v
    NeutralLevel _ v -> namesIn v
    UnreducedLevel v -> namesIn v

-- For QName literals!
instance NamesIn t => NamesIn (Literal' t) where
  namesIn l = case l of
    LitNat{}      -> Set.empty
    LitWord64{}   -> Set.empty
    LitString{}   -> Set.empty
    LitChar{}     -> Set.empty
    LitFloat{}    -> Set.empty
    LitQName _  x -> namesIn x
    LitMeta{}     -> Set.empty
    LitTerm _ t   -> namesIn t

instance NamesIn a => NamesIn (Elim' a) where
  namesIn (Apply arg) = namesIn arg
  namesIn (Proj _ f)  = namesIn f
  namesIn (IApply x y arg) = namesIn (x, y, arg)

instance NamesIn QName   where namesIn x = Set.singleton x  -- interesting case
instance NamesIn ConHead where namesIn h = namesIn (conName h)

instance NamesIn a => NamesIn (Open a)  where

instance NamesIn DisplayForm where
  namesIn (Display _ ps v) = namesIn (ps, v)

instance NamesIn DisplayTerm where
  namesIn v = case v of
    DWithApp v us es -> namesIn (v, us, es)
    DCon c _ vs      -> namesIn (c, vs)
    DDef f es        -> namesIn (f, es)
    DDot v           -> namesIn v
    DTerm v          -> namesIn v

instance NamesIn QuotedTerm where
  namesIn q = namesIn (quotedTerm q, quotedType q)

-- Pattern synonym stuff --

newtype PSyn = PSyn A.PatternSynDefn
instance NamesIn PSyn where
  namesIn (PSyn (_args, p)) = namesIn p

instance NamesIn (A.Pattern' a) where
  namesIn p = case p of
    A.VarP{}               -> Set.empty
    A.ConP _ c args        -> namesIn (c, args)
    A.ProjP _ _ d          -> namesIn d
    A.DefP _ f args        -> namesIn (f, args)
    A.WildP{}              -> Set.empty
    A.AsP _ _ p            -> namesIn p
    A.AbsurdP{}            -> Set.empty
    A.LitP l               -> namesIn l
    A.PatternSynP _ c args -> namesIn (c, args)
    A.RecP _ fs            -> namesIn fs
    A.DotP{}               -> __IMPOSSIBLE__    -- Dot patterns are not allowed in pattern synonyms
    A.EqualP{}             -> __IMPOSSIBLE__    -- Andrea: should we allow these in pattern synonyms?
    A.WithP _ p            -> namesIn p

instance NamesIn AmbiguousQName where
  namesIn (AmbQ cs) = namesIn cs
