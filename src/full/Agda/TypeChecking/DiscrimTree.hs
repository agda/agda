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

import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad

import Agda.TypeChecking.DiscrimTree.Types

import Agda.TypeChecking.Reduce

import qualified Agda.Utils.Trie as Trie
import Agda.Utils.Impossible
import Agda.Utils.Trie (Trie(..))

termKeyElims :: Elims -> Maybe [Term]
termKeyElims = fmap (map unArg) . allApplyElims

-- | Split a term into a 'Key' and some arguments. The 'Key' indicates
-- whether or not the 'Term' is in head-normal form, and provides a
-- quick way to match on the head.
--
-- The 'Int' argument indicates how free a variable must be to be
-- considered a 'LocalK'.
--
-- Presently, non-head-normal terms end up with an empty argument list.
splitTermKey :: Int -> Term -> TCM (Key, [Term])
splitTermKey local tm = reduce tm >>= \case

  Def q as | Just as <- termKeyElims as -> do
    def <- theDef <$> getConstInfo q
    let arity = length as

    -- TODO: Would probably be more accurate to check if there's a
    -- blocker?
    case def of
      Axiom{}    -> pure (RigidK q arity, as)
      Datatype{} -> pure (RigidK q arity, as)
      Record{}   -> pure (RigidK q arity, as)
      _          -> pure (FlexK, as)

  -- When adding a quantified instance, we record how many 'Pi's we went
  -- under, and only variables beyond those are considered LocalK. The
  -- others are considered FlexK since they're "pattern variables" of
  -- the instance.
  Var i as    | Just as <- termKeyElims as, i >= local -> pure (LocalK i (length as), as)

  -- TODO: Could also try to handle eta equality here, I guess?
  Con ch _ as | Just as <- termKeyElims as -> pure (RigidK (conName ch) (length as), as)

  Pi dom ret
    -- For slightly more accurate matching, we decompose non-dependent
    -- 'Pi's into a distinguished key.
    | NoAbs _ b <- ret -> pure (FunK, [unEl (unDom dom), unEl b])
    | otherwise        -> pure (PiK, [])

  _ -> pure (FlexK, [])

termPath :: Int -> [Key] -> [Term] -> TCM [Key]
termPath local acc []        = pure $! reverse acc
termPath local acc (tm:todo) = do
  (k, as) <- splitTermKey local tm
  termPath local (k:acc) (as <> todo)

insertDT :: (Ord a, PrettyTCM a) => Int -> Term -> a -> DiscrimTree a -> TCM (DiscrimTree a)
insertDT local key val tree = do
  path <- termPath local [] [key]
  let it = singletonDT path val
  reportSDoc "tc.instance.discrim.add" 20 $ vcat
    [ "added value" <+> prettyTCM val <+> "to discrimination tree with case"
    , nest 2 (prettyTCM it)
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
lookupDT term tree = match [term] tree where

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
    splitTermKey 0 t >>= \case
      (FlexK, args) -> do
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
        let sp' = sp0 ++ args ++ sp1

        branches <- explore sp0 sp1 args $ Map.toList branches
        rest <- match sp' rest

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
      [ "match" <+> prettyTCM ts
      , prettyTCM tree
      ]
    __IMPOSSIBLE__
    -- TODO (Amy, 2024-02-12): Is it really? Padding the argument list
    -- when exploring might not be enough.
