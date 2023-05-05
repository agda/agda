
module Agda.Syntax.Internal.Blockers where

import Control.DeepSeq

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup

import GHC.Generics (Generic)

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal.Elim

import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.Functor

---------------------------------------------------------------------------
-- * Blocked Terms
---------------------------------------------------------------------------

-- | Even if we are not stuck on a meta during reduction
--   we can fail to reduce a definition by pattern matching
--   for another reason.
data NotBlocked' t
  = StuckOn (Elim' t)
    -- ^ The 'Elim' is neutral and blocks a pattern match.
  | Underapplied
    -- ^ Not enough arguments were supplied to complete the matching.
  | AbsurdMatch
    -- ^ We matched an absurd clause, results in a neutral 'Def'.
  | MissingClauses QName
    -- ^ We ran out of clauses for 'QName', all considered clauses
    --   produced an actual mismatch.
    --   This can happen when try to reduce a function application
    --   but we are still missing some function clauses.
    --   See "Agda.TypeChecking.Patterns.Match".
  | ReallyNotBlocked
    -- ^ Reduction was not blocked, we reached a whnf
    --   which can be anything but a stuck @'Def'@.
  deriving (Show, Generic)

-- | 'ReallyNotBlocked' is the unit.
--   'MissingClauses' is dominant.
--   @'StuckOn'{}@ should be propagated, if tied, we take the left.
instance Semigroup (NotBlocked' t) where
  ReallyNotBlocked <> b = b
  -- MissingClauses is dominant (absorptive)
  b@MissingClauses{} <> _ = b
  _ <> b@MissingClauses{} = b
  -- StuckOn is second strongest
  b@StuckOn{}      <> _ = b
  _ <> b@StuckOn{}      = b
  b <> _                = b

instance Monoid (NotBlocked' t) where
  -- ReallyNotBlocked is neutral
  mempty  = ReallyNotBlocked
  mappend = (<>)

instance NFData t => NFData (NotBlocked' t)

-- | What is causing the blocking? Or in other words which metas or problems need to be solved to
--   unblock the blocked computation/constraint.
data Blocker = UnblockOnAll (Set Blocker)
             | UnblockOnAny (Set Blocker)
             | UnblockOnMeta MetaId     -- ^ Unblock if meta is instantiated
             | UnblockOnProblem ProblemId
             | UnblockOnDef QName       -- ^ Unblock when function is defined
  deriving (Show, Eq, Ord, Generic)

instance NFData Blocker

alwaysUnblock :: Blocker
alwaysUnblock = UnblockOnAll Set.empty

neverUnblock :: Blocker
neverUnblock = UnblockOnAny Set.empty

unblockOnAll :: Set Blocker -> Blocker
unblockOnAll us =
  case allViewS us of
    us | [u] <- Set.toList us -> u
    us                        -> UnblockOnAll us
  where
    allViewS = Set.unions . map allView . Set.toList
    allView (UnblockOnAll us) = allViewS us
    allView u                 = Set.singleton u

unblockOnAny :: Set Blocker -> Blocker
unblockOnAny us =
  case anyViewS us of
    us | [u] <- Set.toList us        -> u
    us | Set.member alwaysUnblock us -> alwaysUnblock
       | otherwise                   -> UnblockOnAny us
  where
    anyViewS = Set.unions . map anyView . Set.toList
    anyView (UnblockOnAny us) = anyViewS us
    anyView u                 = Set.singleton u

unblockOnEither :: Blocker -> Blocker -> Blocker
unblockOnEither a b = unblockOnAny $ Set.fromList [a, b]

unblockOnBoth :: Blocker -> Blocker -> Blocker
unblockOnBoth a b = unblockOnAll $ Set.fromList [a, b]

unblockOnMeta :: MetaId -> Blocker
unblockOnMeta = UnblockOnMeta

unblockOnProblem :: ProblemId -> Blocker
unblockOnProblem = UnblockOnProblem

unblockOnDef :: QName -> Blocker
unblockOnDef = UnblockOnDef

unblockOnAllMetas :: Set MetaId -> Blocker
unblockOnAllMetas = unblockOnAll . Set.mapMonotonic unblockOnMeta

unblockOnAnyMeta :: Set MetaId -> Blocker
unblockOnAnyMeta = unblockOnAny . Set.mapMonotonic unblockOnMeta

onBlockingMetasM :: Monad m => (MetaId -> m Blocker) -> Blocker -> m Blocker
onBlockingMetasM f (UnblockOnAll bs)    = unblockOnAll . Set.fromList <$> mapM (onBlockingMetasM f) (Set.toList bs)
onBlockingMetasM f (UnblockOnAny bs)    = unblockOnAny . Set.fromList <$> mapM (onBlockingMetasM f) (Set.toList bs)
onBlockingMetasM f (UnblockOnMeta x)    = f x
onBlockingMetasM f b@UnblockOnProblem{} = pure b
onBlockingMetasM f b@UnblockOnDef{}     = pure b

allBlockingMetas :: Blocker -> Set MetaId
allBlockingMetas (UnblockOnAll us)  = Set.unions $ map allBlockingMetas $ Set.toList us
allBlockingMetas (UnblockOnAny us)  = Set.unions $ map allBlockingMetas $ Set.toList us
allBlockingMetas (UnblockOnMeta x)  = Set.singleton x
allBlockingMetas UnblockOnProblem{} = Set.empty
allBlockingMetas UnblockOnDef{}     = Set.empty

allBlockingProblems :: Blocker -> Set ProblemId
allBlockingProblems (UnblockOnAll us)    = Set.unions $ map allBlockingProblems $ Set.toList us
allBlockingProblems (UnblockOnAny us)    = Set.unions $ map allBlockingProblems $ Set.toList us
allBlockingProblems UnblockOnMeta{}      = Set.empty
allBlockingProblems (UnblockOnProblem p) = Set.singleton p
allBlockingProblems UnblockOnDef{}       = Set.empty

allBlockingDefs :: Blocker -> Set QName
allBlockingDefs (UnblockOnAll us)  = Set.unions $ map allBlockingDefs $ Set.toList us
allBlockingDefs (UnblockOnAny us)  = Set.unions $ map allBlockingDefs $ Set.toList us
allBlockingDefs UnblockOnMeta{}    = Set.empty
allBlockingDefs UnblockOnProblem{} = Set.empty
allBlockingDefs (UnblockOnDef q)   = Set.singleton q

{- There are two possible instances of Semigroup, so we don't commit
   to either one.
instance Semigroup Blocker where
  x <> y = unblockOnAll $ Set.fromList [x, y]

instance Monoid Blocker where
  mempty = alwaysUnblock
  mappend = (<>)
-}

instance Pretty Blocker where
  pretty (UnblockOnAll us)      = "all" <> parens (fsep $ punctuate "," $ map pretty $ Set.toList us)
  pretty (UnblockOnAny us)      = "any" <> parens (fsep $ punctuate "," $ map pretty $ Set.toList us)
  pretty (UnblockOnMeta m)      = pretty m
  pretty (UnblockOnProblem pid) = "problem" <+> pretty pid
  pretty (UnblockOnDef q)       = "definition" <+> pretty q

-- | Something where a meta variable may block reduction. Notably a top-level meta is considered
--   blocking. This did not use to be the case (pre Aug 2020).
data Blocked' t a
  = Blocked    { theBlocker      :: Blocker,       ignoreBlocking :: a }
  | NotBlocked { blockingStatus  :: NotBlocked' t, ignoreBlocking :: a }
  deriving (Show, Functor, Foldable, Traversable, Generic)

instance Decoration (Blocked' t) where
  traverseF f (Blocked b x)     = Blocked b <$> f x
  traverseF f (NotBlocked nb x) = NotBlocked nb <$> f x

-- | Blocking on _all_ blockers.
instance Applicative (Blocked' t) where
  pure = notBlocked
  f <*> e = ((f $> ()) `mappend` (e $> ())) $> ignoreBlocking f (ignoreBlocking e)

instance Semigroup a => Semigroup (Blocked' t a) where
  Blocked x a    <> Blocked y b    = Blocked (unblockOnBoth x y) (a <> b)
  b@Blocked{}    <> NotBlocked{}   = b
  NotBlocked{}   <> b@Blocked{}    = b
  NotBlocked x a <> NotBlocked y b = NotBlocked (x <> y) (a <> b)

instance (Semigroup a, Monoid a) => Monoid (Blocked' t a) where
  mempty = notBlocked mempty
  mappend = (<>)

instance (NFData t, NFData a) => NFData (Blocked' t a)

-- | When trying to reduce @f es@, on match failed on one
--   elimination @e ∈ es@ that came with info @r :: NotBlocked@.
--   @stuckOn e r@ produces the new @NotBlocked@ info.
--
--   'MissingClauses' must be propagated, as this is blockage
--   that can be lifted in the future (as more clauses are added).
--
--   @'StuckOn' e0@ is also propagated, since it provides more
--   precise information as @StuckOn e@ (as @e0@ is the original
--   reason why reduction got stuck and usually a subterm of @e@).
--   An information like @StuckOn (Apply (Arg info (Var i [])))@
--   (stuck on a variable) could be used by the lhs/coverage checker
--   to trigger a split on that (pattern) variable.
--
--   In the remaining cases for @r@, we are terminally stuck
--   due to @StuckOn e@.  Propagating @'AbsurdMatch'@ does not
--   seem useful.
--
--   'Underapplied' must not be propagated, as this would mean
--   that @f es@ is underapplied, which is not the case (it is stuck).
--   Note that 'Underapplied' can only arise when projection patterns were
--   missing to complete the original match (in @e@).
--   (Missing ordinary pattern would mean the @e@ is of function type,
--   but we cannot match against something of function type.)
stuckOn :: Elim' t -> NotBlocked' t -> NotBlocked' t
stuckOn e = \case
    r@MissingClauses{} -> r
    r@StuckOn{}        -> r
    Underapplied     -> r'
    AbsurdMatch      -> r'
    ReallyNotBlocked -> r'
  where r' = StuckOn e

---------------------------------------------------------------------------
-- * Handling blocked terms.
---------------------------------------------------------------------------

blockedOn :: Blocker -> a -> Blocked' t a
blockedOn b | alwaysUnblock == b = notBlocked
            | otherwise          = Blocked b

blocked :: MetaId -> a -> Blocked' t a
blocked = Blocked . unblockOnMeta

notBlocked :: a -> Blocked' t a
notBlocked = NotBlocked ReallyNotBlocked

blocked_ :: MetaId -> Blocked' t ()
blocked_ x = blocked x ()

notBlocked_ :: Blocked' t ()
notBlocked_ = notBlocked ()

getBlocker :: Blocked' t a -> Blocker
getBlocker (Blocked b _) = b
getBlocker NotBlocked{}  = neverUnblock

-----------------------------------------------------------------------------
-- * Waking up logic
-----------------------------------------------------------------------------

-- | Should a constraint wake up or not? If not, we might refine the unblocker.
data WakeUp = WakeUp | DontWakeUp (Maybe Blocker)
  deriving (Show, Eq)

wakeUpWhen :: (constr -> Bool) -> (constr -> WakeUp) -> constr -> WakeUp
wakeUpWhen guard wake c | guard c   = wake c
                        | otherwise = DontWakeUp Nothing

wakeUpWhen_ :: (constr -> Bool) -> constr -> WakeUp
wakeUpWhen_ p = wakeUpWhen p (const WakeUp)

wakeIfBlockedOnProblem :: ProblemId -> Blocker -> WakeUp
wakeIfBlockedOnProblem pid u
  | u' == alwaysUnblock = WakeUp
  | otherwise           = DontWakeUp (Just u')
  where
    u' = unblockProblem pid u

wakeIfBlockedOnMeta :: MetaId -> Blocker -> WakeUp
wakeIfBlockedOnMeta x u
  | u' == alwaysUnblock = WakeUp
  | otherwise           = DontWakeUp (Just u')
  where
    u' = unblockMeta x u

wakeIfBlockedOnDef :: QName -> Blocker -> WakeUp
wakeIfBlockedOnDef q u
  | u' == alwaysUnblock = WakeUp
  | otherwise           = DontWakeUp (Just u')
  where
    u' = unblockDef q u

unblockMeta :: MetaId -> Blocker -> Blocker
unblockMeta x u@(UnblockOnMeta y) | x == y    = alwaysUnblock
                                  | otherwise = u
unblockMeta _ u@UnblockOnProblem{} = u
unblockMeta _ u@UnblockOnDef{}     = u
unblockMeta x (UnblockOnAll us)    = unblockOnAll $ Set.map (unblockMeta x) us
unblockMeta x (UnblockOnAny us)    = unblockOnAny $ Set.map (unblockMeta x) us

unblockProblem :: ProblemId -> Blocker -> Blocker
unblockProblem p u@(UnblockOnProblem q) | p == q    = alwaysUnblock
                                        | otherwise = u
unblockProblem _ u@UnblockOnMeta{} = u
unblockProblem _ u@UnblockOnDef{}  = u
unblockProblem p (UnblockOnAll us) = unblockOnAll $ Set.map (unblockProblem p) us
unblockProblem p (UnblockOnAny us) = unblockOnAny $ Set.map (unblockProblem p) us

unblockDef :: QName -> Blocker -> Blocker
unblockDef q u@(UnblockOnDef q') | q == q'   = alwaysUnblock
                                 | otherwise = u
unblockDef q u@UnblockOnMeta{} = u
unblockDef q u@UnblockOnProblem{} = u
unblockDef q (UnblockOnAll us) = unblockOnAll $ Set.map (unblockDef q) us
unblockDef q (UnblockOnAny us) = unblockOnAny $ Set.map (unblockDef q) us
