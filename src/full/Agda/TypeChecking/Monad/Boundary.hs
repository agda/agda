-- | Functions for working with 'Boundary'-sensitive elaboration
module Agda.TypeChecking.Monad.Boundary
  ( withBoundaryAsHints, discardBoundary
  , withBoundary
  , withBoundaryHint
  , withTermOrNot
  , eliminateAlongBoundary
  , reifyBoundary
  , normaliseBoundary
  , normaliseBoundary'

  , Boundary'(..), Boundary
  , BoundaryConstraint'(..), BoundaryConstraint
  )
  where

import Control.DeepSeq ( NFData )
import Control.Monad ( unless, forM, when )
import Control.Arrow (first)

import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Foldable (for_)
import Data.Maybe (isNothing)
import Data.IntMap (IntMap)

import GHC.Generics (Generic)

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal

import qualified Agda.Utils.SmallSet as SmallSet
import qualified Agda.Utils.Pretty as P

import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Closure ( enterClosure )
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Trace (MonadTrace(traceCall))
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env (modifyAllowedReductions)

import Control.Monad.Except (MonadError (catchError), throwError)
import Agda.TypeChecking.Substitute.Class

import Agda.TypeChecking.MetaVars (newLevelMeta)
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Level
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce ( simplify )
import Agda.TypeChecking.Pretty
    ( (<+>), vcat, PrettyTCM(prettyTCM), prettyList_, parens )

import Agda.Interaction.Options.Base (PragmaOptions(..))

import Agda.TypeChecking.Primitive.Cubical.Base ( combineSys', imin )
import Agda.TypeChecking.Primitive.Base ( (<#>), (<@>), argN )
import Data.Data

data BoundaryConstraint' term
  = BoundaryConstraint
    { boundaryCofib   :: term
      -- ^ The cofibration (invariant: must have type I)
    , boundaryFace    :: term
      -- ^ The wanted RHS
    , boundaryDisplay :: Maybe [(term, Bool)]
      -- ^ A list of @(term = i0/i1)@ constraints, computed by
      -- 'normaliseBoundary', used for pretty-printing.
    , boundaryCheck   :: Bool
      -- ^ Should this boundary be checked during type-checking?
    }
  deriving (Functor, Generic, Foldable, Traversable)

-- | Represents the boundary of an elaboration context.
--
-- Each pair in boundaryFaces can be imagined to represent an Agda
-- expression of type 'Σ I λ φ → Partial φ A', where 'A' is the current
-- type. Correspondingly, if we do not know the current type, or it is
-- not a fibrant type, then 'boundaryFaces' must be empty.
newtype Boundary' term
  = Boundary { boundaryFaces :: [BoundaryConstraint' term] }
  deriving (Functor, Generic, Foldable, Traversable)

type BoundaryConstraint = BoundaryConstraint' Term
type Boundary = Boundary' Term

instance NFData t => NFData (BoundaryConstraint' t)
instance NFData t => NFData (Boundary' t)

-- | "Normalise" a 'Boundary'. Note that this does not perform actual
-- normalisation on the right-hand-sides (for that, use the
-- 'Traversable' 'Boundary'' instance). Instead, 'normaliseBoundary'
-- will:
--
--   1. Put the formulae in disjunctive normal form. While boundary
--   constraints introduced by IApply copatterns are in DNF by
--   construction, it is possible for φ to be a disjunction e.g. because
--   of Sub or hcomp).
--
--   2. Apply interval substitutions coming from the normalised formulae
--   to the right-hand-sides. For example, a boundary constraint @i ⊢ p
--   i@ will normalise to @i ⊢ p i1@, which will be simplified to
--   whatever @p@'s right endpoint is (if @p i@ is an 'IApply').
normaliseBoundary'
  :: Bool
  -- ^ Should the right-hand-sides be reduced or should we only put the
  -- boundary in DNF and compute display forms?
  -> Boundary
  -> TCM Boundary
normaliseBoundary' dfonly (Boundary []) = pure (Boundary [])
normaliseBoundary' dfonly (Boundary faces) = do
  unview <- intervalUnview'
  let
    io = unview IOne
    iz = unview IZero
    inot i = unview (INeg (argN i))
    imin x y = unview (IMin (argN x) (argN y))
  faces <- forM faces $ \bc@(BoundaryConstraint phi rhs _ check) -> do
    -- We don't enforce that the boundary φs are disjunction-free, so we
    -- normalise them here:
    let reblocked = pure bc
    ctx <- buildClosure ()
    forallFaceMaps' phi (\_ _ _ -> reblocked) $ \faces sub -> do
      let
        reconstructed = [ if x then var i else inot (var i) | (i, x) <- IntMap.toList faces ]
        psi = case reconstructed of
          [] -> io
          [x] -> x
          (x:xs) -> foldr imin x xs
      -- the substitution from forallFaceMaps will have dropped all
      -- variables mentioned in faces from the context, so we need to,
      -- for each of those variables, bring the term up one to "escape"
      -- from the forallFaceMaps.
      let escape tm = applySubst (foldr (\(i, _) sub -> raiseFromS i 1 `composeS` sub) idS (IntMap.toAscList faces)) tm
      enterClosure ctx $ \_ -> reportSDoc "tc.boundary" 30 $ vcat $
        [ "orig  " <+> prettyTCM phi <+> "⊢" <+> prettyTCM rhs
        , "tsigma" <+> prettyTCM (applySubst sub rhs)
        , "escape" <+> prettyTCM (escape (applySubst sub rhs))
        , "faces " <+> prettyTCM (fmap (first var) (IntMap.toList faces))
        ]
      rhs' <-
        if dfonly
          then pure rhs
          else escape <$> simplify (applySubst sub rhs)

      -- But the variables in the faces IntMap refer to their indices in
      -- the original context, so we're ok to just return psi.
      -- Additionally, we compute a display form for this clause here.
      pure (BoundaryConstraint psi rhs' (Just (fmap (first var) (IntMap.toList faces))) check)
  pure (Boundary (concat faces))

normaliseBoundary :: Boundary -> TCM Boundary
normaliseBoundary = normaliseBoundary' False

-- | Attempt to reify the given 'Boundary' constraints as an extension
-- of the given 'Type'. Returns 'Nothing' if the given type isn't
-- fibrant.
reifyBoundary :: Type -> Boundary -> TCM (Maybe Term)
reifyBoundary ty boundary = do
  Boundary faces <- normaliseBoundary boundary
  m <- primSub
  case getSort ty of
    Type x -> runNamesT [] $ do
      lev <- reallyUnLevelView x
      [lev, ty] <- traverse open [lev, unEl ty]
      (phi, sys) <- combineSys' lev ty =<< traverse (\(BoundaryConstraint a b _ _) -> (,) <$> open a <*> open b) faces
      Just <$> (pure m <#> lev <@> ty <@> pure phi <@> pure sys)
    _ -> pure Nothing

-- | Run the continuation in a context where all the boundary
-- constraints are treated as hints only, but keep track of how to
-- verify that a given term matches the boundary.
withBoundaryAsHints
  :: (MonadConversion m, MonadTCEnv m, MonadDebug m, MonadTrace m)
  => ((Comparison -> Type -> Term -> m ()) -> m a)
  -- ^ The argument given to this function is a term comparison function
  -- (e.g. 'compareTerm'), but it will additionally trace that we are
  -- verifying a particular boundary formula. This results in better
  -- error messages than using e.g. 'compareTermOnFace' directly.
  -> m a
withBoundaryAsHints k = do
  boundary <- boundaryFaces <$> asksTC envBoundary
  unless (null boundary) $
    reportSDoc "tc.boundary" 30 $ "Discarding boundary" <+> vcat (prettyTCM <$> boundary)
  let
    cont cmp ty term = verboseBracket "tc.boundary" 30 "recoverBoundary" $ do
      reportSDoc "tc.boundary" 30 $ vcat
        [ "Reviving discarded boundary as comparison problem"
        , prettyTCM term <+> ":" <+> prettyTCM boundary
        ]

      for_ boundary $ \con@(BoundaryConstraint phi rhs _ check) -> when check $ do
        r <- asksTC envRange
        traceCall (CheckTermBoundary r con ty term) $ compareTermOnFace cmp phi ty term rhs

  localTC (\e -> e { envBoundary = Boundary ((\x -> x { boundaryCheck = False}) <$> boundary) }) $ k $
    if null boundary
      then (\_ _ _ -> pure ())
      else cont

-- | Run the continuation in a context without boundary constraints, but
-- keep track of how to verify that a given term matches the boundary.
discardBoundary
  :: (MonadConversion m, MonadTCEnv m, MonadDebug m, MonadTrace m)
  => ((Comparison -> Type -> Term -> m ()) -> m a)
  -- ^ The argument given to this function is a term comparison function
  -- (e.g. 'compareTerm'), but it will additionally trace that we are
  -- verifying a particular boundary formula. This results in better
  -- error messages than using e.g. 'compareTermOnFace' directly.
  -> m a
discardBoundary k = withBoundaryAsHints $ localTC (\e -> e {envBoundary = Boundary []}) . k

-- | Add the given constraints to the 'Boundary' in the current context.
-- The new constraints are not automatically checked for consistency
-- with any pre-existing constraints, so it is up to the caller of
-- 'withBoundary' to ensure that, for each pair of constraints
-- @(φ, x)@ and @(ψ, y)@ we must have @φ ∧ ψ ⊢ x = y@.
withBoundary
  :: (MonadTCEnv m, MonadDebug m, MonadConversion m, HasBuiltins m)
  => [(Term, Term)]
  -> m a
  -> m a
withBoundary ts k = do
  boundary <- boundaryFaces <$> asksTC envBoundary
  let ts' = map (\(a, b) -> BoundaryConstraint a b Nothing True) ts
  localTC (\e -> e { envBoundary = Boundary (ts' ++ boundaryFaces (envBoundary e)) }) k

-- | Add a boundary constraint to the environment that will not be
-- checked: it serves only as a hint, and **MUST** be checked by
-- IApplyConfluence later.
withBoundaryHint
  :: (MonadTCEnv m, MonadDebug m, MonadConversion m, HasBuiltins m)
  => [(Term, Term)]
  -> m a
  -> m a
withBoundaryHint ts k = do
  boundary <- boundaryFaces <$> asksTC envBoundary
  let ts' = map (\(a, b) -> BoundaryConstraint a b Nothing False) ts
  localTC (\e -> e { envBoundary = Boundary (ts' ++ boundaryFaces (envBoundary e)) }) k

-- | Helper function for adding a boundary problem of the form
-- @(φ ∨ ~ φ) ⊢ primPOr φ (~ φ) x y@
withTermOrNot
  :: (MonadTCEnv m, MonadDebug m, MonadConversion m, HasBuiltins m)
  => Term         -- φ
  -> (Term, Term) -- The boundary when (φ = i1) and when (φ = i0), respectively
  -> m a
  -> m a
withTermOrNot what (yeswhat, notwhat) k = do
  cubical <- optCubical <$> pragmaOptions
  case cubical of
    Just _ -> do
      neg <- primINeg
      -- put ~φ before φ in case φ is a variable
      withBoundary [(neg `apply` [argN what], notwhat), (what, yeswhat)] k
    Nothing -> k

-- | Apply a list of eliminations to the boundary constraints. When
-- going into an introduction form, if the type has a corresponding
-- elimination form, then instead of discarding the boundary, we can
-- refine it by that elimination.
--
-- E.g. instead of discarding the boundary when checking a lambda
-- abstraction, we can refine the boundary by applying the 0th variable.
eliminateAlongBoundary  :: (MonadTCEnv m) => Elims -> m a -> m a
eliminateAlongBoundary es =
  localTC (\e -> e { envBoundary = Boundary $ map go (boundaryFaces (envBoundary e)) })
  where go b = b { boundaryFace = boundaryFace b `applyE` es }

instance PrettyTCM t => PrettyTCM (BoundaryConstraint' t) where
  prettyTCM (BoundaryConstraint _ b (Just phi) _) =
    let
      disp (x, True)  = parens $ prettyTCM x <+> "= i1"
      disp (x, False) = parens $ prettyTCM x <+> "= i0"
    in prettyList_ (map disp phi) <+> "⊢" <+> prettyTCM b
  prettyTCM (BoundaryConstraint phi b _ _) =
    prettyTCM phi <+> "⊢" <+> prettyTCM b

instance P.Pretty t => P.Pretty (BoundaryConstraint' t) where
  pretty (BoundaryConstraint _ b (Just phi@(_:_)) _) =
    let
      disp (x, True)  = P.parens $ P.pretty x P.<+> "= i1"
      disp (x, False) = P.parens $ P.pretty x P.<+> "= i0"
    in P.prettyList_ (map disp phi) P.<+> "⊢" P.<+> P.pretty b
  pretty (BoundaryConstraint phi b _ _) =
    P.pretty phi P.<+> "⊢" P.<+> P.pretty b
