module Agda.TypeChecking.Opacity
  ( saturateOpaqueBlocks
  , isAccessibleDef
  , hasAccessibleDef
  )
  where

import Control.Monad.State.Strict
import Control.Monad

import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as Map
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.Map.Strict (Map)
import Data.Foldable
import Data.Maybe

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Common

import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad

import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Lens

-- | Ensure that opaque blocks defined in the current module have
-- transitively-closed unfolding sets.
saturateOpaqueBlocks :: forall m. (MonadTCState m, ReadTCState m, MonadFresh OpaqueId m, MonadDebug m, MonadTrace m, MonadWarning m) => m ()
saturateOpaqueBlocks = entry where
  entry = do
    known   <- useTC stOpaqueBlocks
    inverse <- useTC stOpaqueIds
    OpaqueId _ ourmod <- fresh

    let
      isOurs (OpaqueId _ mod, _) = mod == ourmod
      ours = snd <$> filter isOurs (Map.toAscList known)
    -- Only compute transitive closure for opaque blocks declared in
    -- the current top-level module. Deserialised blocks are always
    -- closed, so this work would be redundant.
    (blocks, names) <- computeClosure known inverse ours

    reportSDoc "tc.opaque" 30 $ vcat $
      text "Opaque blocks defined in this module:":map pretty ours

    modifyTC' $ \st -> st { stPostScopeState = (stPostScopeState st)
      { stPostOpaqueBlocks = blocks
      , stPostOpaqueIds    = names
      } }

  -- Actually compute the closure.
  computeClosure
    :: Map OpaqueId OpaqueBlock
      -- Accumulates the satured opaque blocks; also contains the
      -- opaque blocks of imported modules.
    -> Map QName OpaqueId
      -- Accumulates a mapping from names to opaque blocks; also
      -- contains imported opaque names.
    -> [OpaqueBlock]
      -- List of our opaque blocks, in dependency order.
    -> m ( Map OpaqueId OpaqueBlock
         , Map QName OpaqueId
         )
  computeClosure !blocks !names [] = pure (blocks, names)
  computeClosure blocks names (block:xs) = setCurrentRange (opaqueRange block) $ do
    let
      yell nm accum = setCurrentRange (getRange nm) $ do
        warning (UnfoldTransparentName nm)
        pure accum
      -- Add the unfolding-set of the given name to the accumulator
      -- value.
      transitive nm accum = fromMaybe (yell nm accum) $ do
        id    <- Map.lookup nm names
        block <- Map.lookup id blocks
        pure . pure $ HashSet.union (opaqueUnfolding block) accum

    -- Compute the transitive closure: bring in names
    --
    --   ... that are defined as immediate children of the opaque block
    --   ... that are unfolded by the parent opaque block
    --   ... that are implied by each name in the unfolding clause.
    closed <- foldrM transitive
      (  opaqueDecls block
      <> foldMap opaqueUnfolding (opaqueParent block >>= flip Map.lookup blocks)
      )
      (opaqueUnfolding block)

    let
      block' = block { opaqueUnfolding = closed }

      -- Update the mapping from names to blocks, so that future
      -- references to names defined in our opaque block will know the
      -- right unfolding set.
      names' = HashSet.foldr (\name -> Map.insert name (opaqueId block)) names
        (opaqueDecls block)

    computeClosure (Map.insert (opaqueId block) block' blocks) names' xs

-- | Decide whether or not a definition is reducible. Returns 'True' if
-- the definition /can/ step.
isAccessibleDef :: TCEnv -> TCState -> Definition -> Bool

-- IgnoreAbstractMode ignores both abstract and opaque. It is used for
-- getting the original definition (for inConcreteOrAbstractMode), and
-- for "normalise ignoring abstract" interactively.
isAccessibleDef env state defn
  | envAbstractMode env == IgnoreAbstractMode = True

-- Otherwise, actually apply the reducibility rules..
isAccessibleDef env state defn =
  let
    -- Reducibility rules for abstract definitions:
    concretise def = case envAbstractMode env of
      -- Being outside an abstract block has no effect on concreteness
      ConcreteMode       -> def

      -- This clause is redundant with the preceding guard but GHC can't
      -- figure it out:
      IgnoreAbstractMode -> ConcreteDef

      AbstractMode
        -- Symbols from enclosing modules will be made concrete:
        | current `isLeChildModuleOf` m -> ConcreteDef

        -- Symbols from child modules, or unrelated modules, will keep
        -- the same concreteness:
        | otherwise                     -> def
      where
        current = dropAnon $ envCurrentModule env
        m       = dropAnon $ qnameModule (defName defn)
        dropAnon (MName ms) = MName $ List.dropWhileEnd isNoName ms

    -- Reducibility rule for opaque definitions: If we are operating
    -- under an unfolding block,
    clarify def = case envCurrentOpaqueId env of
      Just oid ->
        let
          block = fromMaybe __IMPOSSIBLE__ $ Map.lookup oid (view stOpaqueBlocks state)

          -- Then any name which is a member of the unfolding-set
          -- associated to that block will be unfolded.
          okay = defName defn `HashSet.member` opaqueUnfolding block
        in if okay then TransparentDef else def
      Nothing -> def

    -- Short-circuit the map lookup for vanilla definitions
    plainDef = defAbstract defn == ConcreteDef
            && defOpaque   defn == TransparentDef

  in plainDef
  || ( concretise (defAbstract defn) == ConcreteDef
    && clarify    (defOpaque defn)   == TransparentDef)

-- | Will the given 'QName' have a proper definition, or will it be
-- wrapped in an 'AbstractDefn'?
hasAccessibleDef
  :: (ReadTCState m, MonadTCEnv m, HasConstInfo m) => QName -> m Bool
hasAccessibleDef qn = do
  env <- askTC
  st <- getTCState
  ignoreAbstractMode $ do
    def <- getConstInfo qn
    pure $ isAccessibleDef env st def
