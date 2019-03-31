{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Generalize
  ( generalizeType
  , generalizeType'
  , generalizeTelescope ) where

import Control.Arrow ((***), first, second)
import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub, partition, init, sortBy)
import Data.Function (on)
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (LensInScope(..))
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Monad (bindVariable)
import Agda.Syntax.Scope.Base (Binder(..))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Abstract
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.InstanceArguments (postponeInstanceConstraints)
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.Benchmarking (Phase(Typing, Generalize))
import Agda.Utils.Benchmark
import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation
import qualified Agda.Utils.Graph.TopSort as Graph

#include "undefined.h"

-- | Generalize a telescope over a set of generalizable variables.
generalizeTelescope :: Map QName Name -> (forall a. (Telescope -> TCM a) -> TCM a) -> ([Maybe Name] -> Telescope -> TCM a) -> TCM a
generalizeTelescope vars typecheckAction ret | Map.null vars = typecheckAction (ret [])
generalizeTelescope vars typecheckAction ret = billTo [Typing, Generalize] $ withGenRecVar $ \ genRecMeta -> do
  let s = Set.fromList (Map.keys vars)
  ((cxtNames, tel, letbinds), namedMetas, allmetas) <-
    createMetasAndTypeCheck s $ typecheckAction $ \ tel -> do
      cxt <- take (size tel) <$> getContext
      lbs <- getLetBindings -- This gives let-bindings valid in the current context
      return (map (fst . unDom) cxt, tel, lbs)
  -- Translate the QName to the corresponding bound variable
  (genTel, genTelNames, sub) <- computeGeneralization genRecMeta namedMetas allmetas

  let boundVar q = fromMaybe __IMPOSSIBLE__ $ Map.lookup q vars
      genTelVars = (map . fmap) boundVar genTelNames

  tel' <- applySubst sub <$> instantiateFull tel

  -- This is not so nice. When changing the context from Γ (r : R) to Γ Δ we need to do this at the
  -- level of contexts (as a Context -> Context function), so we repeat the name logic here. Take
  -- care to preserve the name of named generalized variables.
  let setName name d = first (const name) <$> d
      cxtEntry (mname, d) = do
          name <- maybe (setNotInScope <$> freshName_ s) return mname
          return $ setName name d
        where s  = fst $ unDom d
      dropCxt err = updateContext (strengthenS err 1) (drop 1)
  genTelCxt <- dropCxt __IMPOSSIBLE__ $ mapM cxtEntry $ reverse $ zip genTelVars $ telToList genTel

  -- For the explicit module telescope we get the names from the typecheck
  -- action.
  let newTelCxt = zipWith setName cxtNames $ reverse $ telToList tel'

  -- We are in context Γ (r : R) and should call the continuation in context Γ Δ Θρ passing it Δ Θρ
  -- We have
  --   Γ (r : R) ⊢ Θ            Θ = tel
  --   Γ ⊢ Δ                    Δ = genTel
  --   Γ Δ ⊢ ρ : Γ (r : R)      ρ = sub
  --   Γ ⊢ Δ Θρ                 Θρ = tel'
  -- And we shouldn't forget about the let-bindings (#3470)
  --   Γ (r : R) Θ ⊢ letbinds
  --   Γ Δ Θρ      ⊢ letbinds' = letbinds(lift |Θ| ρ)
  letbinds' <- applySubst (liftS (size tel) sub) <$> instantiateFull letbinds
  let addLet (x, (v, dom)) = addLetBinding' x v dom

  updateContext sub ((genTelCxt ++) . drop 1) $
    updateContext (raiseS (size tel')) (newTelCxt ++) $
      foldr addLet (ret genTelVars $ abstract genTel tel') letbinds'


-- | Generalize a type over a set of (used) generalizable variables.
generalizeType :: Set QName -> TCM Type -> TCM ([Maybe QName], Type)
generalizeType s typecheckAction = do
  (ns, t, _) <- generalizeType' s $ (,()) <$> typecheckAction
  return (ns, t)

-- | Allow returning additional information from the type checking action.
generalizeType' :: Set QName -> TCM (Type, a) -> TCM ([Maybe QName], Type, a)
generalizeType' s typecheckAction = billTo [Typing, Generalize] $ withGenRecVar $ \ genRecMeta -> do

  ((t, userdata), namedMetas, allmetas) <- createMetasAndTypeCheck s typecheckAction
  (genTel, genTelNames, sub) <- computeGeneralization genRecMeta namedMetas allmetas

  t' <- abstract genTel . applySubst sub <$> instantiateFull t

  reportSDoc "tc.generalize" 40 $ vcat
    [ "generalized"
    , nest 2 $ "t =" <+> escapeContext 1 (prettyTCM t') ]

  return (genTelNames, t', userdata)

-- | Create metas for the generalizable variables and run the type check action.
createMetasAndTypeCheck :: Set QName -> TCM a -> TCM (a, Map MetaId QName, IntSet)
createMetasAndTypeCheck s typecheckAction = do
  ((namedMetas, x), allmetas) <- metasCreatedBy $ do
    (metamap, genvals) <- createGenValues s
    x <- locallyTC eGeneralizedVars (const genvals) typecheckAction
    return (metamap, x)
  return (x, namedMetas, allmetas)

-- | Add a placeholder variable that will be substituted with a record value packing up all the
--   generalized variables.
withGenRecVar :: (Type -> TCM a) -> TCM a
withGenRecVar ret = do
  -- Create a meta type (in Set₀) for the telescope record. It won't
  -- necessarily fit in Set₀, but since it's only used locally the sort
  -- shouldn't matter. Another option would be to put it in Setω, which is a
  -- bit more honest, but this leads to performance problems (see #3306).
  genRecMeta <- newTypeMeta (mkType 0)
  addContext (defaultDom ("genTel" :: String, genRecMeta)) $ ret genRecMeta

-- | Compute the generalized telescope from metas created when checking the type/telescope to be
--   generalized. Called in the context extended with the telescope record variable (whose type is
--   the first argument). Returns the telescope of generalized variables and a substitution from
--   this telescope to the current context.
computeGeneralization :: Type -> Map MetaId name -> IntSet -> TCM (Telescope, [Maybe name], Substitution)
computeGeneralization genRecMeta nameMap allmetas = postponeInstanceConstraints $ do
  -- Pair metas with their metaInfo
  mvs <- mapM ((\ x -> (x,) <$> lookupMeta x) . MetaId) $ IntSet.toList allmetas

  constrainedMetas <- Set.unions <.> mapM (constraintMetas . clValue . theConstraint) =<<
                        ((++) <$> useTC stAwakeConstraints
                              <*> useTC stSleepingConstraints)

  let isConstrained x = Set.member x constrainedMetas
      -- Note: Always generalize named metas even if they are constrained. We
      -- freeze them so they won't be instantiated by the constraint, and we do
      -- want the nice error from checking the constraint after generalization.
      -- See #3276.
      isGeneralizable (x, mv) = Map.member x nameMap ||
                                not (isConstrained x) && YesGeneralize == unArg (miGeneralizable (mvInfo mv))
      isSort = isSortMeta_ . snd
      isOpen = isOpenMeta . mvInstantiation . snd

  -- Split the generalizable metas in open and closed
  let (generalizable, nongeneralizable)         = partition isGeneralizable mvs
      (generalizableOpen', generalizableClosed) = partition isOpen generalizable
      (openSortMetas, generalizableOpen)        = partition isSort generalizableOpen'
      nongeneralizableOpen                      = filter isOpen nongeneralizable

  -- Issue 3301: We can't generalize over sorts
  case openSortMetas of
    [] -> return ()
    ms -> warning $ CantGeneralizeOverSorts (map fst ms)

  -- Any meta in the solution of a generalizable meta should be generalized over (if possible).
  cp <- viewTC eCurrentCheckpoint
  let canGeneralize x | isConstrained x = return False
      canGeneralize x = do
          mv   <- lookupMeta x
          msub <- enterClosure (miClosRange $ mvInfo mv) $ \ _ ->
                    checkpointSubstitution' cp
          let sameContext =
                -- We can only generalize if the metavariable takes the context variables of the
                -- current context as arguments. This happens either when the context of the meta
                -- is the same as the current context and there is no pruning, or the meta context
                -- is a weakening but the extra variables have been pruned.
                -- It would be possible to generalize also in the case when some context variables
                -- (other than genTel) have been pruned, but it's hard to construct an example
                -- where this actually happens.
                case (msub, mvPermutation mv) of
                  (Just IdS, Perm m xs)        -> xs == [0 .. m - 1]
                  (Just (Wk n IdS), Perm m xs) -> xs == [0 .. m - n - 1]
                  _                            -> False
          when (not sameContext) $ do
            ty <- getMetaType x
            let Perm m xs = mvPermutation mv
            reportSDoc "tc.generalize" 20 $ vcat
              [ text "Don't know how to generalize over"
              , nest 2 $ prettyTCM x <+> text ":" <+> prettyTCM ty
              , text "in context"
              , nest 2 $ inTopContext . prettyTCM =<< getContextTelescope
              , text "permutation:" <+> text (show (m, xs))
              , text "subst:" <+> pretty msub ]
          return sameContext
  inherited <- fmap Set.unions $ forM generalizableClosed $ \ (x, mv) ->
    case mvInstantiation mv of
      InstV _ v -> do
        parentName <- getMetaNameSuggestion x
        metas <- filterM canGeneralize . allMetas =<< instantiateFull v
        let suggestNames i [] = return ()
            suggestNames i (m : ms)  = do
              name <- getMetaNameSuggestion m
              case name of
                "" -> do
                  setMetaNameSuggestion m (parentName ++ "." ++ show i)
                  suggestNames (i + 1) ms
                _  -> suggestNames i ms
        Set.fromList metas <$ suggestNames 1 metas
      _ -> __IMPOSSIBLE__

  let (alsoGeneralize, reallyDontGeneralize) = partition (`Set.member` inherited) $ map fst nongeneralizableOpen
      generalizeOver = map fst generalizableOpen ++ alsoGeneralize

  -- Sort metas in dependency order
  sortedMetas <- sortMetas generalizeOver

  let dropCxt err = updateContext (strengthenS err 1) (drop 1)

  -- Create the pre-record type (we don't yet know the types of the fields)
  (genRecName, genRecCon, genRecFields) <- dropCxt __IMPOSSIBLE__ $
      createGenRecordType genRecMeta sortedMetas

  -- Solve the generalizable metas. Each generalizable meta is solved by projecting the
  -- corresponding field from the genTel record.
  cxtTel <- getContextTelescope
  let solve m field = do
        -- m should not be instantiated, but if we don't check constraints
        -- properly it could be (#3666 and #3667). Fail hard instead of
        -- generating bogus types.
        whenM (isInstantiatedMeta m) __IMPOSSIBLE__
        assignTerm' m (telToArgs cxtTel) $ Var 0 [Proj ProjSystem field]
  zipWithM_ solve sortedMetas genRecFields

  -- Record the named variables in the telescope
  let telNames = map (`Map.lookup` nameMap) sortedMetas

  -- Build the telescope of generalized metas
  teleTypes <- do
    args <- getContextArgs
    fmap concat $ forM sortedMetas $ \ m -> do
      mv   <- lookupMeta m
      let info = getArgInfo $ miGeneralizable $ mvInfo mv
          HasType{ jMetaType = t } = mvJudgement mv
      return [(Arg info $ miNameSuggestion $ mvInfo mv, piApply t args)]
  let genTel = buildGeneralizeTel genRecCon teleTypes
  reportSDoc "tc.generalize" 40 $ vcat
    [ text "genTel =" <+> prettyTCM genTel ]

  -- Fill in the missing details of the telescope record.
  dropCxt __IMPOSSIBLE__ $ fillInGenRecordDetails genRecName genRecCon genRecFields genRecMeta genTel

  -- Now abstract over the telescope. We need to apply the substitution that subsitutes a record
  -- value packing up the generalized variables for the genTel variable.
  let sub = unpackSub genRecCon (map (argInfo . fst) teleTypes) (length teleTypes)

  -- Finally eta-expand the GenTel record in non-generalized open metas. When
  -- we do also update interaction points to refer to the eta-expanded meta
  -- (#3340).

  let inscope (ii, InteractionPoint{ipMeta = Just x})
        | IntSet.member (metaId x) allmetas = [(x, ii)]
      inscope _ = []
  ips <- Map.fromList . concatMap inscope . Map.toList <$> useTC stInteractionPoints

  cp  <- viewTC eCurrentCheckpoint
  forM_ reallyDontGeneralize $ \ x -> do
    mv <- lookupMeta x
    when (isOpenMeta $ mvInstantiation mv) $ enterClosure (miClosRange $ mvInfo mv) $ \ _ -> do
      cxt <- instantiateFull =<< getContext
      let notPruned = [ i | i <- permute (takeP (length cxt) $ mvPermutation mv) $
                                 reverse $ zipWith const [0..] cxt ]
      case [ i | (i, Dom{unDom = (_, El _ (Def q _))}) <- zip [(0::Int)..] cxt,
                 q == genRecName, elem i notPruned ] of
        []    -> return ()
        _:_:_ -> __IMPOSSIBLE__
        [i] -> do
          -- Get the substitution from the point of generalization to the current
          -- context. This always succeeds since if the meta depends on GenTel
          -- it must have been created inside the generalization.
          δ <- checkpointSubstitution cp

          reportSDoc "tc.generalize.eta" 30 $ vcat
            [ "eta expanding GenRec in"
            , nest 2 $ prettyTCM (mvJudgement mv)
            , nest 2 $ "GenRecTel is var" <+> pretty i ]

          -- So we have
          --   Γ (r : GenTel) Δ ⊢ x : A  and
          --   Γ (r : GenTel) Δ ⊢ δ : Γ₀ (r : GenTel)
          -- where |Δ| = i and r has not been pruned.
          a <- case mvJudgement mv of
                 IsSort{}  -> return Nothing
                 HasType{} -> Just <$> getMetaTypeInContext x

          -- v is x applied to the context variables
          v <- MetaV x . map Apply <$> getMetaContextArgs mv

          -- Now we want to compute a substitution
          --   Γ Θ ⊢ σ : Γ (r : GenTel)
          -- eta expanding the GenTel (actually this is just 'sub', since 'sub'
          -- is polymorphic in Γ)
          let σ = sub

          -- We also need Θ, which is genTel but in Γ instead of Γ₀. We don't
          -- have a substitution from Γ to Γ₀ so we have rebuild the telescope.
          let name = traverse $ \ (s, ty) -> (,ty) <$> freshName_ s
              -- Γ₀ (r : GenTel) ⊢ teleTypes
              -- and we need something in Γ (r : GenTel)
              -- The teleTypes should not depend on Δ, so we can apply δ and
              -- strenghten:
              -- Γ (r : GenTel) ⊢ γ : Γ₀ (r : GenTel)
              γ = composeS (strengthenS __IMPOSSIBLE__ i) δ
          theta <- mapM name $ telToList $ buildGeneralizeTel genRecCon $ applySubst γ teleTypes

          -- We can get into the unpacked context by lifting with i:
          --   Γ Θ Δσ ⊢ ρ : Γ (r : GenTel) Δ
          let ρ = liftS i σ
              -- we need to perform the same operation on the 'Context'
              expand cxt = deltaRσ ++ thetaR ++ gammaR
                where
                  (deltaR, _ : gammaR) = splitAt i cxt
                  thetaR = reverse theta
                  -- Remember that deltaR is a list and not a telescope. We
                  -- need to manage lifting manually.
                  deltaRσ = go (length deltaR - 1) deltaR
                    where
                      -- Γ (r : GenTel) Δ₁ ⊢ x, where |Δ₁| = i
                      -- Γ Θ Δ₁σ ⊢ liftS i σ : Γ (r : GenTel) Δ₁
                      go i (x : xs) = applySubst (liftS i σ) x : go (i - 1) xs
                      go _ []       = []

          -- We don't need it, but for documentation purposes here is the
          -- inverse of ρ:
          -- Γ (r : GenTel) Δ ⊢ ρ⁻¹ : Γ Θ Δρ
          let ρinv = liftS i $ [ Var 0 [Proj ProjSystem fld] | fld <- reverse $ genRecFields ] ++# raiseS 1

          reportSDoc "tc.generalize.eta" 50 $ nest 2 $ vcat
            [ "ρ ∘ ρ⁻¹ =" <+> pretty (composeS ρ ρinv)
            , "ρ⁻¹ ∘ ρ =" <+> pretty (composeS ρinv ρ) ]

          -- #3519: don't leak the fresh meta if we didn't expand
          speculateTCState_ $ updateContext ρ expand $ do
            reportSDoc "tc.generalize.eta" 30 $ nest 2 $
              "new context:" <+> (inTopContext . prettyTCM =<< getContextTelescope)
            -- In this context we create a fresh meta Γ Θ Δσ ⊢ y : Aρ
            (y, u) <- localScope $ do

              -- First, we add the named variables to the scope, to allow
              -- them to be used in holes (#3341).
              forM_ theta $ \ Dom{ unDom = (x, _) } -> do
                -- Recognize named variables by lack of '.' (TODO: hacky!)
                reportSLn "tc.generalize.eta.scope" 40 $ "Adding (or not) " ++ show (nameConcrete x) ++ " to the scope"
                when ('.' `notElem` show (nameConcrete x)) $ do
                  reportSLn "tc.generalize.eta.scope" 40 "  (added)"
                  bindVariable LambdaBound (nameConcrete x) x

              case a of
                Nothing -> do
                  s@(MetaS y _) <- newSortMeta
                  return (y, Sort s)
                Just a  -> newNamedValueMeta DontRunMetaOccursCheck
                                             (miNameSuggestion $ mvInfo mv)
                                             (applySubst ρ a)

            -- Finally we solve xρ := y. Meta assignment is smart enough to
            -- treat the GenRec constructor application produced by ρ as a
            -- Miller pattern.
            let MetaV _ es = applySubst ρ v
                Just vs    = allApplyElims es

            reportSDoc "tc.generalize.eta" 30 $ nest 2 $
              hsep ["assigning", prettyTCM (MetaV x es), ":=", prettyTCM u]

            -- This fails if x is a blocked term. We leave those alone.
            do  assign DirEq x vs u
                -- If x is a hole, update the hole to point to y instead. Note that
                -- holes never point to blocked metas.
                whenJust (Map.lookup x ips) (`connectInteractionPoint` y)
                return SpeculateCommit

              `catchError_` \ case
                PatternErr{} -> do
                  reportSDoc "tc.generalize.eta" 20 $ nest 2 $
                    "Skipping eta expansion of blocked term meta" <+> pretty (MetaV x es)
                  return SpeculateAbort  -- roll back state changes
                err -> throwError err


  return (genTel, telNames, sub)

-- | Create a substition from a context where the i first record fields are variables to a context
--   where you have a single variable of the record type. Packs up the field variables in a record
--   constructor and pads with __DUMMY_TERM__s for the missing fields. Important that you apply this
--   to terms that only projects the defined fields from the record variable.
--   Used with partial record values when building the telescope of generalized variables in which
--   case we have done the dependency analysis that guarantees it is safe.
unpackSub :: ConHead -> [ArgInfo] -> Int -> Substitution
unpackSub con infos i = recSub
  where
    ar = length infos
    appl info v = Apply (Arg info v)
    recVal = Con con ConOSystem $ zipWith appl infos $ [var j | j <- [i - 1, i - 2..0]] ++ replicate (ar - i) __DUMMY_TERM__

    -- want: Γ Δᵢ ⊢ recSub i : Γ (r : R)
    -- have:
    -- Γ Δᵢ ⊢ recVal i :# σ : Θ (r : R),  if Γ Δᵢ ⊢ σ : Θ
    -- Γ Δᵢ ⊢ WkS i IdS : Γ
    recSub = recVal :# Wk i IdS

-- | Takes the list of types
--    A₁ []
--    A₂ [r.f₁]
--    A₃ [r.f₂, r.f₃]
--    ...
--   And builds the telescope
--    (x₁ : A₁ [ r := c _       .. _ ])
--    (x₂ : A₂ [ r := c x₁ _    .. _ ])
--    (x₃ : A₃ [ r := c x₁ x₂ _ .. _ ])
--    ...
buildGeneralizeTel :: ConHead -> [(Arg String, Type)] -> Telescope
buildGeneralizeTel con xs = go 0 xs
  where
    infos = map (argInfo . fst) xs
    recSub i = unpackSub con infos i
    go _ [] = EmptyTel
    go i ((name, ty) : xs) = ExtendTel (dom ty') $ Abs (unArg name) $ go (i + 1) xs
      where ty' = applySubst (recSub i) ty
            dom = defaultNamedArgDom (getArgInfo name) (unArg name)

-- | Create metas for all used generalizable variables and their dependencies.
createGenValues :: Set QName -> TCM (Map MetaId QName, Map QName GeneralizedValue)
createGenValues s = do
  genvals <- locallyTC eGeneralizeMetas (const YesGeneralize) $
               forM (sortBy (compare `on` getRange) $ Set.toList s) createGenValue
  let metaMap = Map.fromList [ (m, x) | (x, m, _) <- genvals ]
      nameMap = Map.fromList [ (x, v) | (x, _, v) <- genvals ]
  return (metaMap, nameMap)

-- | Create a generalisable meta for a generalisable variable.
createGenValue :: QName -> TCM (QName, MetaId, GeneralizedValue)
createGenValue x = do
  cp  <- viewTC eCurrentCheckpoint
  def <- instantiateDef =<< getConstInfo x
                   -- Only prefix of generalizable arguments (for now?)
  let nGen       = case defArgGeneralizable def of
                     NoGeneralizableArgs     -> 0
                     SomeGeneralizableArgs n -> n
      ty         = defType def
      TelV tel _ = telView' ty
      -- Generalizable variables are never explicit, so if they're given as
      -- explicit we default to hidden.
      hideExplicit arg | visible arg = hide arg
                       | otherwise   = arg
      argTel     = telFromList $ map hideExplicit $ take nGen $ telToList tel

  args <- newTelMeta argTel

  let metaType = piApply ty args
      name     = show (nameConcrete $ qnameName x)
  (m, term) <- newNamedValueMeta DontRunMetaOccursCheck name metaType

  -- Freeze the meta to prevent named generalizable metas to be instantiated.
  updateMetaVar m $ \ mv -> mv { mvFrozen = Frozen }

  -- Set up names of arg metas
  forM_ (zip3 [1..] (map unArg args) (telToList argTel)) $ \ case
    (i, MetaV m _, Dom{unDom = (x, _)}) -> do
      let suf "_" = show i
          suf ""  = show i
          suf x   = x
      setMetaNameSuggestion m (name ++ "." ++ suf x)
    _ -> return ()  -- eta expanded

  -- Update the ArgInfos for the named meta. The argument metas are
  -- created with the correct ArgInfo.
  setMetaArgInfo m $ hideExplicit (defArgInfo def)

  reportSDoc "tc.generalize" 50 $ vcat
    [ "created metas for generalized variable" <+> prettyTCM x
    , nest 2 $ "top  =" <+> prettyTCM term
    , nest 2 $ "args =" <+> prettyTCM args ]

  case term of
    MetaV{} -> return ()
    _       -> genericDocError =<< ("Cannot generalize over" <+> prettyTCM x <+> "of eta-expandable type") <?>
                                    prettyTCM metaType
  return (x, m, GeneralizedValue{ genvalCheckpoint = cp
                                , genvalTerm       = term
                                , genvalType       = metaType })

-- | Sort metas in dependency order.
sortMetas :: [MetaId] -> TCM [MetaId]
sortMetas metas = do
  metaGraph <- fmap concat $ forM metas $ \ m -> do
                  deps <- nub . filter (`elem` metas) . allMetas <$> (instantiateFull =<< getMetaType m)
                  return [ (m, m') | m' <- deps ]

  caseMaybe (Graph.topSort metas metaGraph)
            (typeError GeneralizeCyclicDependency)
            return

-- | Create a not-yet correct record type for the generalized telescope. It's not yet correct since
--   we haven't computed the telescope yet, and we need the record type to do it.
createGenRecordType :: Type -> [MetaId] -> TCM (QName, ConHead, [QName])
createGenRecordType genRecMeta@(El genRecSort _) sortedMetas = do
  current <- currentModule
  let freshQName s = qualify current <$> freshName_ (s :: String)
      mkFieldName  = freshQName . (generalizedFieldName ++) <=< getMetaNameSuggestion
  genRecFields <- mapM (defaultArg <.> mkFieldName) sortedMetas
  genRecName   <- freshQName "GeneralizeTel"
  genRecCon    <- freshQName "mkGeneralizeTel" <&> \ con -> ConHead
                  { conName      = con
                  , conInductive = Inductive
                  , conFields    = genRecFields }
  forM_ (zip sortedMetas genRecFields) $ \ (meta, fld) -> do
    fieldTy <- getMetaType meta
    let field = unArg fld
    addConstant field $ defaultDefn (argInfo fld) field fieldTy $
      let proj = Projection { projProper   = Just genRecName
                            , projOrig     = field
                            , projFromType = defaultArg genRecName
                            , projIndex    = 1
                            , projLams     = ProjLams [defaultArg "gtel"] } in
      Function { funClauses      = []
               , funCompiled     = Nothing
               , funSplitTree    = Nothing
               , funTreeless     = Nothing
               , funInv          = NotInjective
               , funMutual       = Just []
               , funAbstr        = ConcreteDef
               , funDelayed      = NotDelayed
               , funProjection   = Just proj
               , funFlags        = Set.empty
               , funTerminates   = Just True
               , funExtLam       = Nothing
               , funWith         = Nothing
               , funCopatternLHS = False
               , funCovering     = []
               }
  addConstant (conName genRecCon) $ defaultDefn defaultArgInfo (conName genRecCon) __DUMMY_TYPE__ $ -- Filled in later
    Constructor { conPars   = 0
                , conArity  = length genRecFields
                , conSrcCon = genRecCon
                , conData   = genRecName
                , conAbstr  = ConcreteDef
                , conInd    = Inductive
                , conComp   = (emptyCompKit, Nothing)
                , conForced = []
                , conErased = []
                }
  let dummyTel 0 = EmptyTel
      dummyTel n = ExtendTel (defaultDom __DUMMY_TYPE__) $ Abs "_" $ dummyTel (n - 1)
  addConstant genRecName $ defaultDefn defaultArgInfo genRecName (sort genRecSort) $
    Record { recPars         = 0
           , recClause       = Nothing
           , recConHead      = genRecCon
           , recNamedCon     = False
           , recFields       = genRecFields
           , recTel          = dummyTel (length genRecFields) -- Filled in later
           , recMutual       = Just []
           , recEtaEquality' = Inferred YesEta
           , recInduction    = Nothing
           , recAbstr        = ConcreteDef
           , recComp         = emptyCompKit }
  reportSDoc "tc.generalize" 40 $ vcat
    [ text "created genRec" <+> text (show genRecFields) ]
  -- Solve the genRecMeta
  args <- getContextArgs
  let genRecTy = El genRecSort $ Def genRecName $ map Apply args
  noConstraints $ equalType genRecTy genRecMeta
  return (genRecName, genRecCon, map unArg genRecFields)

-- | Once we have the generalized telescope we can fill in the missing details of the record type.
fillInGenRecordDetails :: QName -> ConHead -> [QName] -> Type -> Telescope -> TCM ()
fillInGenRecordDetails name con fields recTy fieldTel = do
  cxtTel <- fmap hideAndRelParams <$> getContextTelescope
  let fullTel = cxtTel `abstract` fieldTel
  -- Field types
  let mkFieldTypes [] EmptyTel = []
      mkFieldTypes (fld : flds) (ExtendTel ty ftel) =
          abstract cxtTel (El s $ Pi (defaultDom recTy) (Abs "r" $ unDom ty)) :
          mkFieldTypes flds (absApp ftel proj)
        where
          s = PiSort (getSort recTy) (Abs "r" $ getSort ty)
          proj = Var 0 [Proj ProjSystem fld]
      mkFieldTypes _ _ = __IMPOSSIBLE__
  let fieldTypes = mkFieldTypes fields (raise 1 fieldTel)
  reportSDoc "tc.generalize" 40 $ text "Field types:" <+> inTopContext (nest 2 $ vcat $ map prettyTCM fieldTypes)
  zipWithM_ setType fields fieldTypes
  -- Constructor type
  let conType = fullTel `abstract` raise (size fieldTel) recTy
  reportSDoc "tc.generalize" 40 $ text "Final genRecCon type:" <+> inTopContext (prettyTCM conType)
  setType (conName con) conType
  -- Record telescope: Includes both parameters and fields.
  modifyGlobalDefinition name $ \ r ->
    r { theDef = (theDef r) { recTel = fullTel } }
  where
    setType q ty = modifyGlobalDefinition q $ \ d -> d { defType = ty }

