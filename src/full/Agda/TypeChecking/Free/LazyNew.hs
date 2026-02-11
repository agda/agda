{-# LANGUAGE AllowAmbiguousTypes, MagicHash #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -ddump-to-file #-}
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}

-- | Computing the free variables of a term lazily.
--
-- We implement a reduce (traversal into monoid) over internal syntax
-- for a generic collection (monoid with singletons).  This should allow
-- a more efficient test for the presence of a particular variable.
--
-- Worst-case complexity does not change (i.e. the case when a variable
-- does not occur), but best case-complexity does matter.  For instance,
-- see 'Agda.TypeChecking.Substitute.mkAbs': each time we construct
-- a dependent function type, we check whether it is actually dependent.
--
-- The distinction between rigid and strongly rigid occurrences comes from:
--   Jason C. Reed, PhD thesis, 2009, page 96 (see also his LFMTP 2009 paper)
--
-- The main idea is that x = t(x) is unsolvable if x occurs strongly rigidly
-- in t.  It might have a solution if the occurrence is not strongly rigid, e.g.
--
--   x = \f -> suc (f (x (\ y -> k)))  has  x = \f -> suc (f (suc k))
--
-- [Jason C. Reed, PhD thesis, page 106]
--
-- Under coinductive constructors, occurrences are never strongly rigid.
-- Also, function types and lambdas do not establish strong rigidity.
-- Only inductive constructors do so.
-- (See issue 1271).
--
-- For further reading on semirings and semimodules for variable occurrence,
-- see e.g. Conor McBrides "I got plenty of nuttin'" (Wadlerfest 2016).
-- There, he treats the "quantity" dimension of variable occurrences.
--
-- The semiring has an additive operation for combining occurrences of subterms,
-- and a multiplicative operation of representing function composition.  E.g.
-- if variable @x@ appears @o@ in term @u@, but @u@ appears in context @q@ in
-- term @t@ then occurrence of variable @x@ coming from @u@ is accounted for
-- as @q o@ in @t@.
--
-- Consider example @(λ{ x → (x,x)}) y@:
--
--   * Variable @x@ occurs once unguarded in @x@.
--
--   * It occurs twice unguarded in the aggregation @x@ @x@
--
--   * Inductive constructor @,@ turns this into two strictly rigid occurrences.
--
--     If @,@ is a record constructor, then we stay unguarded.
--
--   * The function @({λ x → (x,x)})@ provides a context for variable @y@.
--     This context can be described as weakly rigid with quantity two.
--
--   * The final occurrence of @y@ is obtained as composing the context with
--     the occurrence of @y@ in itself (which is the unit for composition).
--     Thus, @y@ occurs weakly rigid with quantity two.
--
-- It is not a given that the context can be described in the same way
-- as the variable occurrence.  However, for quantity it is the case
-- and we obtain a semiring of occurrences with 0, 1, and even ω, which
-- is an absorptive element for addition.

module Agda.TypeChecking.Free.LazyNew where

import Control.Applicative hiding (empty)
import Control.Monad.Reader (MonadReader(..))
import GHC.Exts

import Agda.Utils.StrictReader
import Agda.Utils.ExpandCase

import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup ( Any(..), All(..) )

import Agda.TypeChecking.Free.Base

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Semigroup
import Agda.Utils.Singleton
import Agda.Utils.Size

--------------------------------------------------------------------------------

class (ExpandCase (Collect r), Monoid (Collect r)) => ComputeFree r where
  type Collect r

  underBinders'     :: Int -> r -> r
  underConstructor' :: ConHead -> Elims -> r -> r
  underModality'    :: Maybe (Modality -> r -> r)
  underFlexRig'     :: Maybe (FlexRig -> r -> r)
  underRelevance'   :: Maybe (Relevance -> r -> r)
  variable'         :: Int -> r -> Collect r
  ignoreSorts'      :: IgnoreSorts

  ignoreSorts'            = IgnoreNot; {-# INLINE ignoreSorts' #-}
  underConstructor' _ _ r = r;         {-# INLINE underConstructor' #-}
  underModality'          = Nothing;   {-# INLINE underModality'    #-}
  underFlexRig'           = Nothing;   {-# INLINE underFlexRig'     #-}
  underRelevance'         = Nothing;   {-# INLINE underRelevance'   #-}

{-# INLINE underBinders #-}
underBinders :: MonadReader r m => ComputeFree r => Int -> m a -> m a
underBinders = local . underBinders'

{-# INLINE underBinder #-}
underBinder :: MonadReader r m => ComputeFree r => m a -> m a
underBinder = underBinders 1

{-# INLINE underConstructor #-}
underConstructor :: MonadReader r m => ComputeFree r => ConHead -> Elims -> m a -> m a
underConstructor hd es = local (underConstructor' hd es)

{-# INLINE underModality #-}
underModality :: MonadReader r m => ComputeFree r => Modality -> m a -> m a
underModality m act = case underModality' of
  Nothing -> act
  Just f  -> local (f m) act

{-# INLINE underRelevance #-}
underRelevance :: MonadReader r m => ComputeFree r => Relevance -> m a -> m a
underRelevance rel act = case underRelevance' of
  Nothing -> act
  Just f  -> local (f rel) act

{-# INLINE underFlexRig #-}
underFlexRig :: MonadReader r m => ComputeFree r => FlexRig -> m a -> m a
underFlexRig fr act = case underFlexRig' of
  Nothing -> act
  Just f  -> local (f fr) act

{-# INLINE variable #-}
variable :: MonadReader r m => ComputeFree r => Int -> m (Collect r)
variable x = variable' x <$!> ask

--------------------------------------------------------------------------------

class Free t where
  freeVars :: ComputeFree r => t -> Reader r (Collect r)

hasProj :: Elims -> Bool
hasProj = \case [] -> False; Proj{}:_ -> True; _:es -> hasProj es

loop :: (Elims -> Term) -> Elims -> Elims -> Term
loop h res es =
  case es of
    []             -> h $! reverse res
    Proj o f : es' -> let !v = defaultArg $! (h $! reverse res) in loop (Def f) [Apply v] es'
    e        : es' -> loop h (e : res) es'

-- | Convert top-level postfix projections into prefix projections.
myUnSpine :: Term -> Term
myUnSpine t = case t of
  Var i es   | hasProj es -> loop (Var i)   [] es
  Def f es   | hasProj es -> loop (Def f)   [] es
  MetaV x es | hasProj es -> loop (MetaV x) [] es
  t -> t

-- -- | Compute freeVar on an Elims, but adjust all entries before the last projection.
-- --   The `Int` argument is the index of the last projection.
-- goProjectedElims :: forall r. ComputeFree r => Int# -> Elims -> Reader r (Collect r)
-- goProjectedElims lasti ts = expand \ret ->
--   let goPE :: Int# -> Int# -> Elims -> Reader r (Collect r)
--       goPE lasti i es = expand \ret -> case es of
--         [] -> ret mempty
--         e:es | isTrue# (i <=# lasti) ->
--                 ret (underModality defaultModality (freeVars e) <> goPE lasti (i +# 1#) es )
--              | otherwise ->
--                 ret (freeVars e <> goPE lasti (i +# 1#) es)
--   in ret $ goPE lasti 0# ts

-- -- | Find the index of the last projection in the spine if there's any.
-- --   Oterwise return (-1).
-- lastProjectionIx :: Elims -> Int#
-- lastProjectionIx = goPIx 0# where
--   goPIx :: Int# -> Elims -> Int#
--   goPIx i = \case
--     []        -> (-1#)
--     Proj{}:es -> case goPIx (i +# 1#) es of (-1#) -> i; i -> i
--     _:es      -> goPIx (i +# 1#) es

instance Free Term where
  freeVars :: forall r. ComputeFree r => Term -> Reader r (Collect r)
  freeVars t = expand \ret ->

    let t' = case (underModality' @r, underFlexRig' @r) of
               (Nothing, Nothing) -> t
               _                  -> myUnSpine t
    in case t' of
      Var n ts   -> ret (variable n <> underFlexRig WeaklyRigid (freeVars ts))
      Def _ ts   -> ret (underFlexRig WeaklyRigid $ freeVars ts)
      MetaV m ts -> ret (underFlexRig (Flexible (singleton m)) $ freeVars ts)

    case t of
      Var n ts   -> ret (variable n <> underFlexRig WeaklyRigid (freeVars ts))
      Def _ ts   -> ret (underFlexRig WeaklyRigid $ freeVars ts)
      MetaV m ts -> ret (underFlexRig (Flexible (singleton m)) $ freeVars ts)

      -- Var n ts -> case (underModality' @r, underFlexRig' @r) of
      --   -- We don't need to adjust anything because of projections.
      --   (Nothing, Nothing) -> ret (variable n <> underFlexRig WeaklyRigid (freeVars ts))

      --   -- #4484: avoid projected variables being treated as StronglyRigid
      --   -- we compute freeVars as if on the result on "unSpine (Var n ts)"
      --   _ -> case lastProjectionIx ts of
      --     (-1#) -> ret (variable n <> underFlexRig WeaklyRigid (freeVars ts))
      --     lasti -> ret (underFlexRig WeaklyRigid (   underModality defaultModality (variable n)
      --                                             <> goProjectedElims lasti ts))

      -- Def _ ts ->  case underModality' @r of
      --   Nothing -> ret (underFlexRig WeaklyRigid $ freeVars ts)
      --   _ -> case lastProjectionIx ts of
      --     (-1#) -> ret (underFlexRig WeaklyRigid $ freeVars ts)
      --     lasti -> ret (underFlexRig WeaklyRigid $ goProjectedElims lasti ts)

      -- MetaV m ts ->
      --   let !fr = Flexible (singleton m) in
      --   case underModality' @r of
      --     Nothing -> ret (underFlexRig fr $ freeVars ts)
      --     _ -> case lastProjectionIx ts of
      --       (-1#) -> ret (underFlexRig fr $ freeVars ts)
      --       lasti -> ret (underFlexRig fr $ goProjectedElims lasti ts)



      -- λ is not considered guarding, as
      -- we cannot prove that x ≡ λy.x is impossible.
      Lam _ t      -> ret (underFlexRig WeaklyRigid $ freeVars t)
      Lit _        -> ret mempty

        -- because we are not in TCM
        -- we cannot query whether we are dealing with a data/record (strongly r.)
        -- or a definition by pattern matching (weakly rigid)
        -- thus, we approximate, losing that x = List x is unsolvable
      Con c _ ts   ->  ret (underConstructor c ts $ freeVars ts)
      -- Pi is not guarding, since we cannot prove that A ≡ B → A is impossible.
      -- Even as we do not permit infinite type expressions,
      -- we cannot prove their absence (as Set is not inductive).
      -- Also, this is incompatible with univalence (HoTT).

      -- András 2026-01-22: the above comment sounds wrong to me. Pi very much has to be definitionally
      -- injective.
      Pi a b       -> ret $ freeVars (a, b) -- TODO: test with "underConstructor"
      Sort s       -> ret $ underRelevance shapeIrrelevant (freeVars s)
      Level l      -> ret $ freeVars l
      DontCare mt  -> ret $ underModality (Modality irrelevant unitQuantity unitCohesion unitPolarity) $ freeVars mt
      Dummy{}      -> ret $ mempty

instance Free t => Free (Elim' t) where
  freeVars e = expand \ret -> case e of
    (Apply t)      -> ret $ freeVars t
    (Proj{})       -> ret $ mempty
    (IApply x y r) -> ret $ freeVars (x,y,r)

instance Free t => Free (Type' t) where
  freeVars :: forall r. ComputeFree r => Type' t -> Reader r (Collect r)
  freeVars ty = expand \ret -> case ty of
    El s t -> case ignoreSorts' @r of
      IgnoreNot -> ret $ freeVars (s, t)
      _         -> ret $ freeVars t

instance Free Sort where
  freeVars :: forall r. ComputeFree r => Sort -> Reader r (Collect r)
  freeVars s = expand \ret ->
    case ignoreSorts' @r of
      IgnoreAll -> ret mempty
      _         -> case s of
        Univ _ a       -> ret $ freeVars a
        Inf _ _        -> ret $ mempty
        SizeUniv       -> ret $ mempty
        LockUniv       -> ret $ mempty
        LevelUniv      -> ret $ mempty
        IntervalUniv   -> ret $ mempty
        PiSort a s1 s2 -> ret $ underFlexRig (Flexible mempty) (freeVars $ unDom a) <>
                                underFlexRig WeaklyRigid (freeVars (s1, s2))
        FunSort s1 s2  -> ret $ freeVars s1 <> freeVars s2
        UnivSort s     -> ret $ underFlexRig WeaklyRigid $ freeVars s
        MetaS x es     -> ret $ underFlexRig (Flexible $ singleton x) $ freeVars es
        DefS _ es      -> ret $ underFlexRig WeaklyRigid $ freeVars es
        DummyS{}       -> ret $ mempty

instance Free t => Free (Maybe t) where
  freeVars mt = expand \ret -> case mt of
    Nothing -> ret mempty
    Just t  -> ret $ freeVars t

instance Free t => Free [t] where
  freeVars ts = expand \ret -> case ts of
    []   -> ret mempty
    t:ts -> ret $ freeVars t <> freeVars ts

instance Free t => Free (List1 t) where
  freeVars ts = expand \ret -> case ts of
    t :| ts -> ret $ freeVars t <> freeVars ts

instance (Free a, Free b) => Free (a, b) where
  {-# INLINE freeVars #-}
  freeVars ab = expand \ret -> case ab of (a, b) -> ret $ freeVars a <> freeVars b

instance (Free a, Free b, Free c) => Free (a, b, c) where
  {-# INLINE freeVars #-}
  freeVars abc = expand \ret -> case abc of (a, b, c) -> ret $ freeVars a <> freeVars b <> freeVars c

instance (Free a, Free b, Free c, Free d) => Free (a, b, c, d) where
  {-# INLINE freeVars #-}
  freeVars abc = expand \ret -> case abc of
    (a, b, c, d) -> ret $ freeVars a <> freeVars b <> freeVars c <> freeVars d

instance (Free a, Free b, Free c, Free d, Free e) => Free (a, b, c, d, e) where
  {-# INLINE freeVars #-}
  freeVars abc = expand \ret -> case abc of
    (a, b, c, d, e) -> ret $ freeVars a <> freeVars b <> freeVars c <> freeVars d <> freeVars e

instance Free Level where
  {-# INLINE freeVars #-}
  freeVars l = expand \ret -> case l of Max _ as -> ret $ freeVars as

instance Free t => Free (PlusLevel' t) where
  {-# INLINE freeVars #-}
  freeVars pl = expand \ret -> case pl of Plus _ l -> ret $ freeVars l

instance Free t => Free (Arg t) where
  {-# INLINE freeVars #-}
  freeVars t = expand \ret ->
    ret $ underModality (getModality t) $ freeVars $ unArg t

instance Free t => Free (Dom t) where
  {-# INLINE freeVars #-}
  freeVars d = expand \ret -> ret $ freeVars (domTactic d, unDom d)

instance Free t => Free (Abs t) where
  freeVars t = expand \ret -> case t of
    Abs   _ b -> ret $ underBinder $ freeVars b
    NoAbs _ b -> ret $ freeVars b

instance Free t => Free (Tele t) where
  freeVars tel = expand \ret -> case tel of
    EmptyTel          -> ret $ mempty
    (ExtendTel t tel) -> ret $ freeVars (t, tel)

instance Free Clause where
  freeVars cl = expand \ret ->
    ret $ underBinders (size $ clauseTel cl) $ freeVars $ clauseBody cl

instance Free EqualityView where
  freeVars ev = expand \ret -> case ev of
    OtherType t                   -> ret $ freeVars t
    IdiomType t                   -> ret $ freeVars t
    EqualityType _r s _eq l t a b -> ret $ freeVars (s, l, (t, a, b))

-- | What's the rigidity of a constructor?
constructorFlexRig :: ConHead -> Elims -> FlexRig' a
constructorFlexRig (ConHead _ _ i fs) es = case i of

  -- Coinductive (record) constructors admit infinite cycles:
  CoInductive -> WeaklyRigid
  -- Inductive constructors do not admit infinite cycles:
  Inductive   | size es == size fs -> StronglyRigid
              | otherwise          -> WeaklyRigid
  -- Jesper, 2020-10-22: Issue #4995: treat occurrences in non-fully
  -- applied constructors as weakly rigid.
  -- Ulf, 2019-10-18: Now the termination checker treats inductive recursive records
  -- the same as datatypes, so absense of infinite cycles can be proven in Agda, and thus
  -- the unifier is allowed to do it too. Test case: test/Succeed/Issue1271a.agda
  -- WAS:
  -- -- Inductive record constructors do not admit infinite cycles,
  -- -- but this cannot be proven inside Agda.
  -- -- Thus, unification should not prove it either.

{-# INLINE defaultUnderConstructor #-}
defaultUnderConstructor :: (Semigroup a, LensFlexRig r a) => ConHead -> Elims -> r -> r
defaultUnderConstructor c h = over lensFlexRig (composeFlexRig (constructorFlexRig c h))

{-# INLINE defaultUnderFlexRig #-}
defaultUnderFlexRig :: (Semigroup a, LensFlexRig r a) => Maybe (FlexRig' a -> r -> r)
defaultUnderFlexRig = Just \fr -> over lensFlexRig (composeFlexRig fr)

{-# INLINE defaultUnderModality #-}
defaultUnderModality :: LensModality r => Maybe (Modality -> r -> r)
defaultUnderModality = Just \m -> mapModality (composeModality m)

{-# INLINE defaultUnderRelevance #-}
defaultUnderRelevance :: LensRelevance r => Maybe (Relevance -> r -> r)
defaultUnderRelevance = Just \rel -> mapRelevance (composeRelevance rel)
