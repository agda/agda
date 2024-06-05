-- | Imperfect discrimination trees for indexing data by internal
-- syntax.
module Agda.TypeChecking.DiscrimTree
  ( insertDT
  , lookupDT, lookupUnifyDT, QueryResult(..)
  , deleteFromDT
  )
  where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Foldable
import Data.Maybe

import Control.Monad.Trans.Maybe
import Control.Monad.Trans
import Control.Monad

import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free

import Agda.TypeChecking.DiscrimTree.Types

import qualified Agda.Utils.ProfileOptions as Profile

import Agda.Utils.Impossible
import Agda.Utils.Trie (Trie(..))

-- | Dummy term to use as a stand-in for expanded eta-records while
-- building instance trees.
etaExpansionDummy :: Term
etaExpansionDummy = Dummy "eta-record argument in instance head" []

-- | Extract a list of arguments from the list of eliminations; If
-- called while *adding* an instance, additionally replace any arguments
-- that might belong to an eta-record by dummy terms.
termKeyElims
  :: Bool      -- ^ Are we adding or looking up an instance?
  -> TCM Type  -- ^ Continuation to compute the type of the arguments in the spine.
  -> [Arg Term] -- ^ The spine.
  -> TCM (Int, [Term])

-- Since the case tree was generated with wildcards everywhere an eta
-- record appeared, if we're *looking up* an instance, we don't have to
-- do the censorship again.
termKeyElims False _ es = pure (length es, map unArg es)

termKeyElims precise ty args = do
  let
    go ty (Arg _ a:as) = flip (ifPiTypeB ty) (patternViolation . getBlocker) \dom ty' -> do

      -- Is this argument an eta record type --- or a blocked value? In
      -- either case, we replace this position by a dummy, to make sure
      -- that eta-equality is respected.
      maybeEta <- ifBlocked (unDom dom) (\_ _ -> pure True) \_ tm ->
        isJust <$> isEtaRecordType tm

      let
        here
          | maybeEta  = etaExpansionDummy
          | otherwise = a

      (k, there) <- addContext dom (go (unAbs ty') as)
      pure (k + 1, here:there)

    go _ [] = pure (0, [])

  ty >>= flip go args

-- | Ticky profiling for the reason behind "inexactness" in instance
-- search. If at some point while narrowing the set of candidates we had
-- to go through all the possibilities, one of these counters is
-- incremented.
tickExplore :: Term -> TCM ()
tickExplore tm = whenProfile Profile.Instances do
  tick "flex term blocking instance"

  case tm of
    Def{}      -> tick "explore: Def"
    Var{}      -> tick "explore: Var"
    Lam _ v
      -- These two are a hunch: just like FunK, it might be worth
      -- optimising for the case where a lambda is constant (which is
      -- easy to handle, by just pretending the term is something else).
      -- These would come up in e.g. Dec (PathP (λ i → Nat) x y)
      | NoAbs{} <- v -> tick "explore: constant function"
      | Abs _ b <- v, not (0 `freeIn` b) -> tick "explore: constant function"

      | otherwise    -> tick "explore: Lam"
    Lit{}      -> tick "explore: Lit"
    Sort{}     -> tick "explore: Sort"
    Level{}    -> tick "explore: Level"
    MetaV{}    -> tick "explore: Meta"
    DontCare{} -> tick "explore: DontCare"
    _ -> pure ()

-- | Split a term into a 'Key' and some arguments. The 'Key' indicates
-- whether or not the 'Term' is in head-normal form, and provides a
-- quick way to match on the head.
--
-- The 'Int' argument indicates how free a variable must be to be
-- considered a 'LocalK'.
--
-- Presently, non-head-normal terms end up with an empty argument list.
splitTermKey :: Bool -> Int -> Term -> TCM (Key, [Term], Blocker)
splitTermKey precise local tm = catchPatternErr (\b -> pure (FlexK, [], b)) do
  (b, tm') <- ifBlocked tm (\b _ -> patternViolation b) (\b -> fmap (b,) . constructorForm)

  case tm' of
    -- Adding a 'Def' to the key poses a few problems when opacity (or
    -- abstractness) are involved (see issue #7304). Suppose we have an
    -- opaque binding `X = Y`, and an opaque instance `C X`. The problem
    -- is as follows:
    --
    --   if we unfold X → Y when adding the instance, then it will not
    --   get recorded as an instance for C X, only C Y; this is 7304b.
    --
    --   if we *don't* unfold X → Y, then it only gets added as an
    --   instance of C X; in opaque blocks where X is allowed to unfold,
    --   we *won't* find it, because we're looking for C Y.
    --
    -- The solution is to throw our hands up and say "not our problem".
    -- The discrimination tree is allowed to return more results than
    -- strictly necessary, after all, so the solution is to add an
    -- instance for *neither* of C X or C Y, but instead, to treat all
    -- 'Def's headed by 'AbstractDefn' as though they were flexible
    -- (think "as though they were metas").
    Def q as | ReallyNotBlocked <- b, (as, _) <- splitApplyElims as -> do
      info <- getConstInfo q
      case theDef info of
        AbstractDefn{} -> pure (FlexK, [], neverUnblock)
        _ -> do
          (arity, as) <- termKeyElims precise (pure (defType info)) as
          pure (RigidK q arity, as, neverUnblock)

    -- When adding a quantified instance, we record how many 'Pi's we went
    -- under, and only variables beyond those are considered LocalK. The
    -- others are considered FlexK since they're "pattern variables" of
    -- the instance.
    Var i as | i >= local, Just as <- allApplyElims as -> do
      let ty = unDom <$> domOfBV i
      (arity, as) <- termKeyElims precise ty as
      pure (LocalK (i - local) arity, as, neverUnblock)

    -- When looking up an instance, it's better to treat variables and
    -- neutral definitions as rigid things regardless of their spines
    -- (especially if they have projections), than it is to try to
    -- represent them accurately.
    Def q as | not precise             -> pure (RigidK q 0, [], neverUnblock)
    Var i as | not precise, i >= local -> pure (LocalK (i - local) 0, [], neverUnblock)

    Con ch _ as | Just as <- allApplyElims as -> do
      let
        q  = conName ch
        ty = defType <$> getConstInfo q
      (arity, as) <- termKeyElims precise ty as
      pure (RigidK q arity, as, neverUnblock)

    Pi dom ret ->
      let
        -- If we're looking at a non-dependent function type, then we
        -- might as well represent the codomain accurately; Otherwise,
        -- turn the codomain into a wildcard.
        --
        -- The use of a dummy term *shouldn't* leak to the user, because
        -- when we call splitTermKey again, it'll be handled by the last
        -- case, and become a FlexK.
        ret' = case isNoAbs (unEl <$> ret) of
          Just b  -> b
          Nothing -> __DUMMY_TERM__
      in pure (PiK, [unEl (unDom dom), ret'], neverUnblock)

    Lam _ body
      -- Constant lambdas come up quite a bit, particularly (in cubical
      -- mode) as the domain of a PathP. Having this trick improves the
      -- indexing of 'Dec' instances in the 1Lab significantly.
      | Just b <- isNoAbs body -> pure (ConstK, [b], neverUnblock)

    -- Probably not a good idea for accurate indexing if universes
    -- overlap literally everything else.
    Sort _ -> pure (SortK, [], neverUnblock)

    _ -> do
      reportSDoc "tc.instance.split" 30 $ pretty tm
      pure (FlexK, [], neverUnblock)

termPath :: Bool -> Int -> [Key] -> [Term] -> TCM [Key]
termPath toplevel local acc []        = pure $! reverse acc
termPath toplevel local acc (tm:todo) = do

  -- We still want to ignore abstractness at the very top-level of
  -- instance heads, for issue #6941, to ensure that each instance ends
  -- up in the right 'class'. See the comment in `splitTermKey` about
  -- abstract definitions.
  (k, as, _) <-
    if toplevel
      then ignoreAbstractMode (splitTermKey True local tm)
      else splitTermKey True local tm

  reportSDoc "tc.instance.discrim.add" 666 $ vcat
    [ "k:  " <+> prettyTCM k
    , "as: " <+> prettyTCM as
    ]
  termPath False local (k:acc) (as <> todo)

-- | Insert a value into the discrimination tree, turning variables into
-- rigid locals or wildcards depending on the given scope.
insertDT
  :: (Ord a, PrettyTCM a)
  => Int   -- ^ Number of variables to consider wildcards, e.g. the number of leading invisible pis in an instance type.
  -> Term  -- ^ The term to use as a key
  -> a
  -> DiscrimTree a
  -> TCM (DiscrimTree a)
insertDT local key val tree = do
  path <- termPath True local [] [key]
  let it = singletonDT path val
  reportSDoc "tc.instance.discrim.add" 20 $ vcat
    [ "added value" <+> prettyTCM val <+> "to discrimination tree with case"
    , nest 2 (prettyTCM it)
    , "its type:"
    , nest 2 (prettyTCM key)
    , "its path:"
    , nest 2 (prettyTCM path)
    ]
  pure $ mergeDT it tree

-- | If a term matches this key, how many arguments does it place on the
-- spine?
keyArity :: Key -> Int
keyArity = \case
  RigidK _ a -> a
  LocalK _ a -> a
  PiK        -> 2
  ConstK     -> 1
  SortK      -> 0
  FlexK      -> 0

data QueryResult a = QueryResult
  { resultValues  :: Set.Set a
  , resultBlocker :: Blocker
  }

instance Ord a => Semigroup (QueryResult a) where
  QueryResult s b <> QueryResult s' b' = QueryResult (s <> s') (b `unblockOnEither` b')

instance Ord a => Monoid (QueryResult a) where
  mempty = QueryResult mempty neverUnblock

setResult :: Set.Set a -> QueryResult a
setResult = flip QueryResult neverUnblock

blockerResult :: Blocker -> QueryResult a
blockerResult = QueryResult Set.empty

-- | Look up a 'Term' in the given discrimination tree, treating local
-- variables as rigid symbols. The returned set is guaranteed to contain
-- everything that could overlap the given key.
lookupDT :: forall a. (Ord a, PrettyTCM a) => Term -> DiscrimTree a -> TCM (QueryResult a)
lookupDT = lookupDT' True

-- | Look up a 'Term' in the given discrimination tree, treating local
-- variables as wildcards.
lookupUnifyDT :: forall a. (Ord a, PrettyTCM a) => Term -> DiscrimTree a -> TCM (QueryResult a)
lookupUnifyDT = lookupDT' False

lookupDT'
  :: forall a. (Ord a, PrettyTCM a)
  => Bool -- ^ Should local variables be treated as rigid?
  -> Term -- ^ The term to use as key
  -> DiscrimTree a
  -> TCM (QueryResult a)
lookupDT' localsRigid term tree = match True [term] tree where

  split :: Term -> TCM (Key, [Term], Blocker)
  split tm | localsRigid = splitTermKey False 0 tm
  split tm = do
    ctx <- getContextSize
    splitTermKey False ctx tm

  ignoreAbstractMaybe :: forall a. Bool -> TCM a -> TCM a
  ignoreAbstractMaybe True  = ignoreAbstractMode
  ignoreAbstractMaybe False = id

  -- Match a spine against *all* clauses.
  explore :: [Term] -> [Term] -> [Term] -> [(Key, DiscrimTree a)] -> TCM (QueryResult a)
  explore sp0 sp1 args bs = do
    let
      cont (key, trie) res = do
        -- At the moment, explore will always be called with empty args.
        -- But even if this restriction is lifted in the future, we have
        -- to be careful about exploring. Consider:
        --
        --   instance
        --     _ : Foo (con x)
        --
        --   ⊢ Foo ?0
        --
        -- Since ?0 might be applied to more or less arguments than the
        -- one argument that is expected to be between sp0 and sp1 after
        -- matching con, we need to make sure that the spine has the
        -- right number of arguments, otherwise the (sp0, t:sp1) pattern
        -- for a Case will fail.
        let
          dummy n = Dummy ("_pad" <> show n) []
          args' = take (keyArity key) (args ++ [ dummy n | n <- [0..] ])

        reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
          [ "explore" <+> prettyTCM key <+> pretty (keyArity key) <+> pretty (length args)
          , nest 2 (prettyTCM trie)
          , "sp0:  " <+> prettyTCM sp0
          , "sp1:  " <+> prettyTCM sp1
          , "args: " <+> prettyTCM args
          , "args':" <+> prettyTCM args'
          ]
        (<> res) <$> match False (sp0 ++ args' ++ sp1) trie

    foldrM cont mempty bs

  match :: Bool -> [Term] -> DiscrimTree a -> TCM (QueryResult a)
  match toplevel ts EmptyDT    = pure mempty
  match toplevel ts (DoneDT t) = setResult t <$ do
    reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
      [ "done" <+> prettyTCM ts
      , "  →" <+> prettyTCM t
      ]

  match toplevel ts tree@(CaseDT i branches rest) | (sp0, t:sp1) <- splitAt i ts = do
    let
      (sp0, t:sp1) = splitAt i ts
      visit k sp' = case Map.lookup k branches of
        Just m  -> match False sp' m
        Nothing -> pure mempty

    unless toplevel $ reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
      [ "match" <+> prettyTCM sp0 <+> ("«" <> prettyTCM t <> "»") <+> prettyTCM sp1
      , prettyTCM tree
      ]

    -- TODO (Amy, 2024-02-12): Could use reduceB in splitTermKey, and
    -- the blocker here, to suspend instances more precisely when there
    -- is an ambiguity.
    ignoreAbstractMaybe toplevel (split t) >>= \case
      (FlexK, args, blocker) -> do

        reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
          [ "flexible term was forced"
          , "t:" <+> (pretty =<< instantiate t)
          , "will explore" <+> pretty (length branches + 1) <+> "branches"
          ]
        tickExplore t

        -- If we have a "flexible head" at this position then instance
        -- search *at this point* degenerates to looking for all
        -- possible matches.
        --
        -- In any nested CaseDTs, however, it's possible for us to
        -- recover and go back to productively matching. Consider:
        --
        --    instance
        --      xa : X T1 A
        --      xb : X T2 B
        --
        --    ⊢ X ?0 A
        --
        -- Since ?0 is way too flabby to narrow which of T1 or T2 should
        -- be taken, we take both. But then we match A against A and B:
        -- this query will only return {xa}.

        branches <- explore sp0 sp1 args $ Map.toList branches
        rest <- match False ts rest

        pure $! rest <> branches <> blockerResult blocker

      (k, args, blocker) -> do
        let sp' = sp0 ++ args ++ sp1

        -- Actually take the branch corresponding to our rigid head.
        branch <- visit k sp'

        -- When exploring the rest of the tree, the value we cased on
        -- has to be put back in the tree. mergeDT does not perform
        -- commuting conversions to ensure that variables aren't
        -- repeatedly cased on.
        rest <- match False ts rest

        pure $! rest <> branch

  match _ ts tree@(CaseDT i _ rest) = do
    reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
      [ "IMPOSSIBLE match" <+> prettyTCM ts
      , prettyTCM tree
      ]
    -- This really is impossible: since each branch is annotated with
    -- its arity, we only take branches corresponding to neutrals which
    -- exploded into enough arguments.
    __IMPOSSIBLE__

-- | Smart constructor for a leaf node.
doneDT :: Set.Set a -> DiscrimTree a
doneDT s | Set.null s = EmptyDT
doneDT s = DoneDT s

-- | Remove a set of values from the discrimination tree. The tree is
-- rebuilt so that cases with no leaves are removed.
deleteFromDT :: Ord a => DiscrimTree a -> Set.Set a -> DiscrimTree a
deleteFromDT dt gone = case dt of
  EmptyDT -> EmptyDT
  DoneDT s ->
    let s' = Set.difference s gone
     in doneDT s'
  CaseDT i s k ->
    let
      del x = case deleteFromDT x gone of
        EmptyDT -> Nothing
        dt'     -> Just dt'

      s' = Map.mapMaybe del s
      k' = deleteFromDT k gone
    in if | Map.null s' -> k'
          | otherwise   -> CaseDT i s' k'
