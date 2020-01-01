
module Agda.TypeChecking.MetaVars.Mention where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

class MentionsMeta t where
  mentionsMetas :: HashSet MetaId -> t -> Bool

mentionsMeta :: MentionsMeta t => MetaId -> t -> Bool
mentionsMeta = mentionsMetas . HashSet.singleton

instance MentionsMeta Term where
  mentionsMetas xs v = case v of
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
    MetaV y args -> HashSet.member y xs || mm args   -- TODO: we really only have to look one level deep at meta args
    where
      mm v = mentionsMetas xs v

instance MentionsMeta Level where
  mentionsMetas xs (Max _ as) = mentionsMetas xs as

instance MentionsMeta PlusLevel where
  mentionsMetas xs (Plus _ a) = mentionsMetas xs a

instance MentionsMeta LevelAtom where
  mentionsMetas xs l = case l of
    MetaLevel m vs   -> HashSet.member m xs || mentionsMetas xs vs
    BlockedLevel m _ -> HashSet.member m xs  -- if it's blocked on a different meta it doesn't matter if it mentions the meta somewhere else
    UnreducedLevel l -> mentionsMetas xs l
    NeutralLevel _ l -> mentionsMetas xs l

instance MentionsMeta Type where
    mentionsMetas xs (El s t) = mentionsMetas xs (s, t)

instance MentionsMeta Sort where
  mentionsMetas xs s = case s of
    Type l     -> mentionsMetas xs l
    Prop l     -> mentionsMetas xs l
    Inf        -> False
    SizeUniv   -> False
    PiSort a s -> mentionsMetas xs (a, s)
    FunSort s1 s2 -> mentionsMetas xs (s1, s2)
    UnivSort s -> mentionsMetas xs s
    MetaS m es -> HashSet.member m xs || mentionsMetas xs es
    DefS d es  -> mentionsMetas xs es
    DummyS{}   -> False

instance MentionsMeta t => MentionsMeta (Abs t) where
  mentionsMetas xs = mentionsMetas xs . unAbs

instance MentionsMeta t => MentionsMeta (Arg t) where
  mentionsMetas xs a | isIrrelevant a = False
  -- ^ we don't have to look inside irrelevant arguments when deciding to wake constraints
  mentionsMetas xs a = mentionsMetas xs (unArg a)

instance MentionsMeta t => MentionsMeta (Dom t) where
  mentionsMetas xs = mentionsMetas xs . unDom

instance MentionsMeta t => MentionsMeta [t] where
  mentionsMetas xs = any (mentionsMetas xs)

instance MentionsMeta t => MentionsMeta (Maybe t) where
  mentionsMetas xs = maybe False (mentionsMetas xs)

instance (MentionsMeta a, MentionsMeta b) => MentionsMeta (a, b) where
  mentionsMetas xs (a, b) = mentionsMetas xs a || mentionsMetas xs b

instance (MentionsMeta a, MentionsMeta b, MentionsMeta c) => MentionsMeta (a, b, c) where
  mentionsMetas xs (a, b, c) = mentionsMetas xs a || mentionsMetas xs b || mentionsMetas xs c

instance MentionsMeta a => MentionsMeta (Closure a) where
  mentionsMetas xs cl = mentionsMetas xs (clValue cl)

instance MentionsMeta Elim where
  mentionsMetas xs Proj{} = False
  mentionsMetas xs (Apply v) = mentionsMetas xs v
  mentionsMetas xs (IApply y0 y1 v) = mentionsMetas xs (y0,y1,v)

instance MentionsMeta a => MentionsMeta (Tele a) where
  mentionsMetas xs EmptyTel = False
  mentionsMetas xs (ExtendTel a b) = mentionsMetas xs (a, b)

instance MentionsMeta ProblemConstraint where
  mentionsMetas xs = mentionsMetas xs . theConstraint

instance MentionsMeta Constraint where
  mentionsMetas xs c = case c of
    ValueCmp _ t u v    -> mm (t, u, v)
    ValueCmpOnFace _ p t u v    -> mm ((p,t), u, v)
    ElimCmp _ _ t v as bs -> mm ((t, v), (as, bs))
    LevelCmp _ u v      -> mm (u, v)
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
    UnquoteTactic bl tac hole goal -> case bl of
      Nothing -> False
      Just m  -> HashSet.member m xs
    CheckMetaInst m     -> True   -- TODO
    where
      mm v = mentionsMetas xs v

instance MentionsMeta CompareAs where
  mentionsMetas xs = \case
    AsTermsOf a -> mentionsMetas xs a
    AsSizes -> False
    AsTypes -> False

-- instance (Ord k, MentionsMeta e) => MentionsMeta (Map k e) where
--   mentionsMeta = traverse mentionsMeta
