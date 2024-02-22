-- | Imperfect discrimination trees for indexing data by internal
-- syntax.
module Agda.TypeChecking.DiscrimTree
  ( insertDT
  , lookupDT
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

etaExpansionDummy :: Term
etaExpansionDummy = Dummy "eta-record argument in instance head" []

-- | Extract a list of arguments from the list of eliminations; If
-- called while *adding* an instance, additionally replace any arguments
-- that might belong to an eta-record by dummy terms.
termKeyElims
  :: Bool     -- ^ Are we adding or looking up an instance?
  -> TCM Type -- ^ Continuation to compute the type of the arguments in the spine.
  -> Elims    -- ^ The spine.
  -> MaybeT TCM (Int, [Term])
termKeyElims precise _ elims | not precise = do
  es <- hoistMaybe (allApplyElims elims)
  pure (length es, map unArg es)

termKeyElims precise ty elims = do
  args <- hoistMaybe (allApplyElims elims)

  let
    go ty (Arg _ a:as) = flip (ifPiTypeB ty) (const mzero) \dom ty' -> do

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

  ty <- lift ty
  go ty args

tickExplore :: Term -> TCM ()
tickExplore tm = whenProfile Profile.Instances do
  tick "flex term blocking instance"

  case tm of
    Def{}      -> tick "explore: Def"
    Var{}      -> tick "explore: Var"
    Lam _ v
      | NoAbs{} <- v -> tick "explore: constant function"
      | otherwise    -> tick "explore: Lam"
    Lit{}      -> tick "explore: Lit"
    Sort{}     -> tick "explore: Sort"
    Level{}    -> tick "explore: Level"
    MetaV{}    -> tick "explore: Meta"
    DontCare{} -> tick "explore: DontCare"
    t@Dummy{}
      | t == etaExpansionDummy -> tick "explore: from eta-expansion"
    _ -> pure ()

-- | Split a term into a 'Key' and some arguments. The 'Key' indicates
-- whether or not the 'Term' is in head-normal form, and provides a
-- quick way to match on the head.
--
-- The 'Int' argument indicates how free a variable must be to be
-- considered a 'LocalK'.
--
-- Presently, non-head-normal terms end up with an empty argument list.
splitTermKey :: Bool -> Int -> Term -> TCM (Key, [Term])
splitTermKey precise local tm = fmap (fromMaybe (FlexK, [])) . runMaybeT $ do
  (b, tm') <- ifBlocked tm (\_ _ -> mzero) (curry pure)

  case tm' of
    Def q as | ReallyNotBlocked <- b -> do
      let ty = defType <$> getConstInfo q
      (arity, as) <- termKeyElims precise ty as
      pure (RigidK q arity, as)

    -- When adding a quantified instance, we record how many 'Pi's we went
    -- under, and only variables beyond those are considered LocalK. The
    -- others are considered FlexK since they're "pattern variables" of
    -- the instance.
    Var i as | i >= local -> do
      let ty = unDom <$> domOfBV i
      (arity, as) <- termKeyElims precise ty as
      pure (LocalK i arity, as)

    Con ch _ as -> do
      let
        q  = conName ch
        ty = defType <$> getConstInfo q
      (arity, as) <- termKeyElims precise ty as
      pure (RigidK q arity, as)

    Pi dom ret
      -- For slightly more accurate matching, we decompose non-dependent
      -- 'Pi's into a distinguished key.
      | NoAbs _ b <- ret -> do
        whenProfile Profile.Conversion $ tick "funk: non-dependent function"
        pure (FunK, [unEl (unDom dom), raise 1 (unEl b)])

      | otherwise -> do
        whenProfile Profile.Conversion $ tick "funk: genuine pi"
        pure (PiK, [])

    _ -> pure (FlexK, [])

termPath :: Int -> [Key] -> [Term] -> TCM [Key]
termPath local acc []        = pure $! reverse acc
termPath local acc (tm:todo) = do
  (k, as) <- splitTermKey True local tm
  reportSDoc "tc.instance.discrim.add" 666 $ vcat
    [ "k:  " <+> prettyTCM k
    , "as: " <+> prettyTCM as
    ]
  termPath local (k:acc) (as <> todo)

insertDT :: (Ord a, PrettyTCM a) => Int -> Term -> a -> DiscrimTree a -> TCM (DiscrimTree a)
insertDT local key val tree = ignoreAbstractMode do
  path <- termPath local [] [key]
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

keyArity :: Key -> Int
keyArity = \case
  RigidK _ a -> a
  LocalK _ a -> a
  FunK       -> 2
  PiK        -> 0
  FlexK      -> 0

-- | Look up a 'Term' in the given discrimination tree. The returned set
-- is guaranteed to contain everything that could overlap the given key.
lookupDT :: forall a. (Ord a, PrettyTCM a) => Term -> DiscrimTree a -> TCM (Set.Set a)
lookupDT term tree = ignoreAbstractMode (match [term] tree) where

  -- Match a spine against *all* clauses.
  explore :: [Term] -> [Term] -> [Term] -> [(Key, DiscrimTree a)] -> TCM (Set.Set a)
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
        (<> res) <$> match (sp0 ++ args' ++ sp1) trie

    foldrM cont mempty bs

  match :: [Term] -> DiscrimTree a -> TCM (Set.Set a)
  match ts EmptyDT    = pure Set.empty
  match ts (DoneDT t) = t <$ do
    reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
      [ "done" <+> prettyTCM ts
      , "  →" <+> prettyTCM t
      ]

  match ts tree@(CaseDT i branches rest) | (sp0, t:sp1) <- splitAt i ts = do
    let
      (sp0, t:sp1) = splitAt i ts
      visit k sp' = case Map.lookup k branches of
        Just m  -> match sp' m
        Nothing -> pure mempty

    reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
      [ "match" <+> prettyTCM sp0 <+> ("«" <> prettyTCM t <> "»") <+> prettyTCM sp1
      , prettyTCM tree
      ]

    -- TODO (Amy, 2024-02-12): Could use reduceB in splitTermKey, and
    -- the blocker here, to suspend instances more precisely when there
    -- is an ambiguity.
    splitTermKey False 0 t >>= \case
      (FlexK, args) -> do

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
        rest <- match ts rest

        pure $! rest <> branches

      (k, args) -> do
        let sp' = sp0 ++ args ++ sp1

        -- Actually take the branch corresponding to our rigid head.
        --
        -- TODO (Amy, 2024-02-12): Need to handle eta equality. I guess
        -- singletonDT can be made type-directed and we can add an EtaDT
        -- to to the discrimination tree type??
        branch <- visit k sp'

        -- Function values get unpacked to their components on the
        -- spine, but proper Π types don't. Since Π-type instances also
        -- apply to function types, we have to explore that branch too,
        -- if our rigid head is a function.
        funIsPi <- case k of
          FunK -> visit PiK (sp0 ++ sp1)
          _    -> pure mempty

        -- When exploring the rest of the tree, the value we cased on
        -- has to be put back in the tree. mergeDT does not perform
        -- commuting conversions to ensure that variables aren't
        -- repeatedly cased on.
        rest <- match ts rest

        pure $! rest <> branch <> funIsPi

  match ts tree@(CaseDT i _ rest) = do
    reportSDoc "tc.instance.discrim.lookup" 99 $ vcat
      [ "IMPOSSIBLE match" <+> prettyTCM ts
      , prettyTCM tree
      ]
    __IMPOSSIBLE__
    -- TODO (Amy, 2024-02-12): Is it really? Padding the argument list
    -- when exploring might not be enough.
