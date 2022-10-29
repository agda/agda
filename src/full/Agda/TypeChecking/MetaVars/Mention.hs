
module Agda.TypeChecking.MetaVars.Mention where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

class MentionsMeta t where
  mentionsMetas :: HashSet MetaId -> t -> Bool

mentionsMeta :: MentionsMeta t => MetaId -> t -> Bool
mentionsMeta = mentionsMetas . HashSet.singleton

instance MentionsMeta Term where
  mentionsMetas xs = \case
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
      mm :: forall t. MentionsMeta t => t -> Bool
      mm = mentionsMetas xs

instance MentionsMeta Level where
  mentionsMetas xs (Max _ as) = mentionsMetas xs as

instance MentionsMeta PlusLevel where
  mentionsMetas xs (Plus _ a) = mentionsMetas xs a

instance MentionsMeta Blocker where
  mentionsMetas xs (UnblockOnAll bs)  = mentionsMetas xs $ Set.toList bs
  mentionsMetas xs (UnblockOnAny bs)  = mentionsMetas xs $ Set.toList bs
  mentionsMetas xs (UnblockOnMeta x)  = HashSet.member x xs
  mentionsMetas xs UnblockOnProblem{} = False
  mentionsMetas xs UnblockOnDef{}     = False

instance MentionsMeta Type where
    mentionsMetas xs (El s t) = mentionsMetas xs (s, t)

instance MentionsMeta Sort where
  mentionsMetas xs = \case
    Type l     -> mentionsMetas xs l
    Prop l     -> mentionsMetas xs l
    Inf _ _    -> False
    SSet l     -> mentionsMetas xs l
    SizeUniv   -> False
    LockUniv   -> False
    IntervalUniv -> False
    PiSort a s1 s2 -> mentionsMetas xs (a, s1, s2)
    FunSort s1 s2 -> mentionsMetas xs (s1, s2)
    UnivSort s -> mentionsMetas xs s
    MetaS m es -> HashSet.member m xs || mentionsMetas xs es
    DefS d es  -> mentionsMetas xs es
    DummyS{}   -> False

instance MentionsMeta t => MentionsMeta (Abs t) where
  mentionsMetas xs = mentionsMetas xs . unAbs

instance MentionsMeta t => MentionsMeta (Arg t) where
  mentionsMetas xs a | isIrrelevant a = False
  -- we don't have to look inside irrelevant arguments when deciding to wake constraints
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
  mentionsMetas xs = \case
    ValueCmp _ t u v    -> mm (t, u, v)
    ValueCmpOnFace _ p t u v    -> mm ((p,t), u, v)
    ElimCmp _ _ t v as bs -> mm ((t, v), (as, bs))
    LevelCmp _ u v      -> mm (u, v)
    SortCmp _ a b       -> mm (a, b)
    UnBlock _           -> True   -- this might be a postponed typechecking
                                  -- problem and we don't have a handle on
                                  -- what metas it depends on
    FindInstance{}      -> True   -- this needs to be woken up for any meta
    IsEmpty r t         -> mm t
    CheckSizeLtSat t    -> mm t
    CheckFunDef{}       -> True   -- not sure what metas this depends on
    HasBiggerSort a     -> mm a
    HasPTSRule a b      -> mm (a, b)
    UnquoteTactic tac hole goal -> False
    CheckDataSort q s   -> mm s
    CheckMetaInst m     -> True   -- TODO
    CheckType t         -> mm t
    CheckLockedVars a b c d -> mm ((a, b), (c, d))
    UsableAtModality _ ms mod t -> mm (ms, t)
    where
      mm :: forall t. MentionsMeta t => t -> Bool
      mm = mentionsMetas xs

instance MentionsMeta CompareAs where
  mentionsMetas xs = \case
    AsTermsOf a -> mentionsMetas xs a
    AsSizes -> False
    AsTypes -> False

-- instance (Ord k, MentionsMeta e) => MentionsMeta (Map k e) where
--   mentionsMeta = traverse mentionsMeta
