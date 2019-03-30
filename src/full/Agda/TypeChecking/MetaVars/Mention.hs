
module Agda.TypeChecking.MetaVars.Mention where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

class MentionsMeta t where
  mentionsMeta :: MetaId -> t -> Bool

instance MentionsMeta Term where
  mentionsMeta x v = case v of
    Var _ args   -> mm args
    Lam _ b      -> mm b
    Lit{}        -> False
    Def _ args   -> mm args
    Con _ _ args -> mm args
    Pi a b       -> mm (a, b)
    Sort s       -> mm s
    Level l      -> mm l
    Dummy{}      -> False
    DontCare v   -> False   -- we don't have to look inside don't cares when deciding to wake constraints
    MetaV y args -> x == y || mm args   -- TODO: we really only have to look one level deep at meta args
    where
      mm v = mentionsMeta x v

instance MentionsMeta Level where
  mentionsMeta x (Max as) = mentionsMeta x as

instance MentionsMeta PlusLevel where
  mentionsMeta x ClosedLevel{} = False
  mentionsMeta x (Plus _ a) = mentionsMeta x a

instance MentionsMeta LevelAtom where
  mentionsMeta x l = case l of
    MetaLevel m vs   -> x == m || mentionsMeta x vs
    BlockedLevel m _ -> x == m    -- if it's blocked on a different meta it doesn't matter if it mentions the meta somewhere else
    UnreducedLevel l -> mentionsMeta x l
    NeutralLevel _ l -> mentionsMeta x l

instance MentionsMeta Type where
    mentionsMeta x (El s t) = mentionsMeta x (s, t)

instance MentionsMeta Sort where
  mentionsMeta x s = case s of
    Type l     -> mentionsMeta x l
    Prop l     -> mentionsMeta x l
    Inf        -> False
    SizeUniv   -> False
    PiSort s1 s2 -> mentionsMeta x (s1, s2)
    UnivSort s -> mentionsMeta x s
    MetaS m es -> x == m || mentionsMeta x es
    DefS d es  -> mentionsMeta x es
    DummyS{}   -> False

instance MentionsMeta t => MentionsMeta (Abs t) where
  mentionsMeta x = mentionsMeta x . unAbs

instance MentionsMeta t => MentionsMeta (Arg t) where
  mentionsMeta x a | isIrrelevant a = False
  -- ^ we don't have to look inside irrelevant arguments when deciding to wake constraints
  mentionsMeta x a = mentionsMeta x (unArg a)

instance MentionsMeta t => MentionsMeta (Dom t) where
  mentionsMeta x = mentionsMeta x . unDom

instance MentionsMeta t => MentionsMeta [t] where
  mentionsMeta x = any (mentionsMeta x)

instance MentionsMeta t => MentionsMeta (Maybe t) where
  mentionsMeta x = maybe False (mentionsMeta x)

instance (MentionsMeta a, MentionsMeta b) => MentionsMeta (a, b) where
  mentionsMeta x (a, b) = mentionsMeta x a || mentionsMeta x b

instance (MentionsMeta a, MentionsMeta b, MentionsMeta c) => MentionsMeta (a, b, c) where
  mentionsMeta x (a, b, c) = mentionsMeta x a || mentionsMeta x b || mentionsMeta x c

instance MentionsMeta a => MentionsMeta (Closure a) where
  mentionsMeta x cl = mentionsMeta x (clValue cl)

instance MentionsMeta Elim where
  mentionsMeta x Proj{} = False
  mentionsMeta x (Apply v) = mentionsMeta x v
  mentionsMeta x (IApply y0 y1 v) = mentionsMeta x (y0,y1,v)

instance MentionsMeta a => MentionsMeta (Tele a) where
  mentionsMeta x EmptyTel = False
  mentionsMeta x (ExtendTel a b) = mentionsMeta x (a, b)

instance MentionsMeta ProblemConstraint where
  mentionsMeta x = mentionsMeta x . theConstraint

instance MentionsMeta Constraint where
  mentionsMeta x c = case c of
    ValueCmp _ t u v    -> mm (t, u, v)
    ValueCmpOnFace _ p t u v    -> mm ((p,t), u, v)
    ElimCmp _ _ t v as bs -> mm ((t, v), (as, bs))
    LevelCmp _ u v      -> mm (u, v)
    TypeCmp _ a b       -> mm (a, b)
    TelCmp a b _ u v    -> mm ((a, b), (u, v))
    SortCmp _ a b       -> mm (a, b)
    Guarded{}           -> False  -- This gets woken up when the problem it's guarded by is solved
    UnBlock _           -> True   -- this might be a postponed typechecking
                                  -- problem and we don't have a handle on
                                  -- what metas it depends on
    FindInstance{}      -> True   -- this needs to be woken up for any meta
    IsEmpty r t         -> mm t
    CheckSizeLtSat t    -> mm t
    CheckFunDef{}       -> True   -- not sure what metas this depends on
    HasBiggerSort a     -> mm a
    HasPTSRule a b      -> mm (a, b)
    UnquoteTactic bl tac hole goal -> Just x == bl
    where
      mm v = mentionsMeta x v

-- instance (Ord k, MentionsMeta e) => MentionsMeta (Map k e) where
--   mentionsMeta = traverse mentionsMeta
