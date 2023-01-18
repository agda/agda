{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Data where

import Prelude hiding (null, not, (&&), (||) )

import Control.Monad.Except ( MonadError(..), ExceptT(..), runExceptT )
import Control.Monad.Trans.Maybe
import Control.Exception as E

import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Interaction.Options.Base

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Views (deepUnscope)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Common
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Scope.Monad

import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Generalize
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(StrictPos))
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Forcing
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings (warning)

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term ( isType_ )

import Agda.Utils.Boolean
import Agda.Utils.Either
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: A.DefInfo -> QName -> UniverseCheck -> A.DataDefParams -> [A.Constructor] -> TCM ()
checkDataDef i name uc (A.DataDefParams gpars ps) cs =
    traceCall (CheckDataDef (getRange name) name ps cs) $ do

        -- Add the datatype module
        addSection (qnameToMName name)

        -- Look up the type of the datatype.
        def <- instantiateDef =<< getConstInfo name
        t   <- instantiateFull $ defType def
        let npars =
              case theDef def of
                DataOrRecSig n -> n
                _              -> __IMPOSSIBLE__

        -- If the data type is erased, then hard compile-time mode is
        -- entered.
        setHardCompileTimeModeIfErased' def $ do

        -- Make sure the shape of the type is visible
        let unTelV (TelV tel a) = telePi tel a
        t <- unTelV <$> telView t

        parNames <- getGeneralizedParameters gpars name

        -- Top level free vars
        freeVars <- getContextSize

        -- The parameters are in scope when checking the constructors.
        dataDef <- bindGeneralizedParameters parNames t $ \ gtel t0 ->
                   bindParameters (npars - length parNames) ps t0 $ \ ptel t0 -> do

            -- The type we get from bindParameters is Θ -> s where Θ is the type of
            -- the indices. We count the number of indices and return s.
            -- We check that s is a sort.
            let TelV ixTel s0 = telView' t0
                nofIxs = size ixTel

            s <- workOnTypes $ do
              -- Andreas, 2016-11-02 issue #2290
              -- Trying to unify the sort with a fresh sort meta which is
              -- defined outside the index telescope is the most robust way
              -- to check independence of the indices.
              -- However, it might give the dreaded "Cannot instantiate meta..."
              -- error which we replace by a more understandable error
              -- in case of a suspected dependency.
              s <- newSortMetaBelowInf
              catchError_ (addContext ixTel $ equalType s0 $ raise nofIxs $ sort s) $ \ err ->
                  if any (`freeIn` s0) [0..nofIxs - 1] then typeError $ SortCannotDependOnItsIndex name t0
                  else throwError err
              reduce s

            withK   <- not <$> withoutKOption
            erasure <- optErasure <$> pragmaOptions
            -- Parameters are always hidden in constructors. If
            -- --erasure is used, then the parameters are erased for
            -- non-indexed data types, and if --with-K is active this
            -- applies also to indexed data types.
            let tel  = abstract gtel ptel
                tel' = applyWhen (erasure && (withK || nofIxs == 0)) (applyQuantity zeroQuantity) .
                       hideAndRelParams <$>
                       tel

            reportSDoc "tc.data.sort" 20 $ vcat
              [ "checking datatype" <+> prettyTCM name
              , nest 2 $ vcat
                [ "type (parameters instantiated):   " <+> prettyTCM t0
                , "type (full):   " <+> prettyTCM t
                , "sort:   " <+> prettyTCM s
                , "indices:" <+> text (show nofIxs)
                , "gparams:" <+> text (show parNames)
                , "params: " <+> text (show $ deepUnscope ps)
                ]
              ]
            let npars = size tel

            -- Change the datatype from an axiom to a datatype with no constructors.
            let dataDef = DatatypeData
                  { _dataPars       = npars
                  , _dataIxs        = nofIxs
                  , _dataClause     = Nothing
                  , _dataCons       = []     -- Constructors are added later
                  , _dataSort       = s
                  , _dataAbstr      = Info.defAbstract i
                  , _dataMutual     = Nothing
                  , _dataPathCons   = []     -- Path constructors are added later
                  , _dataTranspIx   = Nothing -- Generated later if nofIxs > 0.
                  , _dataTransp     = Nothing -- Added later
                  }

            escapeContext impossible npars $ do
              addConstant' name defaultArgInfo t $ DatatypeDefn dataDef
                -- polarity and argOcc.s determined by the positivity checker

            -- Check the types of the constructors
            pathCons <- forM cs $ \ c -> do
              isPathCons <- checkConstructor name uc tel' nofIxs s c
              return $ if isPathCons == PathCons then Just (A.axiomName c) else Nothing


            -- cubical: the interval universe does not contain datatypes
            -- similar: SizeUniv, ...
            checkDataSort name s

            -- when `--without-K`, all the indices should fit in the
            -- sort of the datatype (see #3420).
            -- Andreas, 2019-07-16, issue #3916:
            -- NoUniverseCheck should also disable the index sort check!
            unless (uc == NoUniverseCheck) $
              whenM withoutKOption $ do
                let s' = case s of
                      Prop l -> Type l
                      _      -> s
                checkIndexSorts s' ixTel

            -- Return the data definition
            return dataDef{ _dataPathCons = catMaybes pathCons
                          }

        let cons   = map A.axiomName cs  -- get constructor names

        (mtranspix, transpFun) <-
          ifM cubicalCompatibleOption
            (do mtranspix <- inTopContext $ defineTranspIx name
                transpFun <- inTopContext $
                               defineTranspFun name mtranspix cons
                                 (_dataPathCons dataDef)
                return (mtranspix, transpFun))
            (return (Nothing, Nothing))

        -- Add the datatype to the signature with its constructors.
        -- It was previously added without them.
        addConstant' name defaultArgInfo t $ DatatypeDefn
            dataDef{ _dataCons = cons
                   , _dataTranspIx = mtranspix
                   , _dataTransp   = transpFun
                   }

-- | Make sure that the target universe admits data type definitions.
--   E.g. @IUniv@, @SizeUniv@ etc. do not accept new constructions.
checkDataSort :: QName -> Sort -> TCM ()
checkDataSort name s = setCurrentRange name $ do
  ifBlocked s postpone {-else-} $ \ _ (s :: Sort) -> do
    let
      yes :: TCM ()
      yes = return ()
      no  :: TCM ()
      no  = typeError $ SortDoesNotAdmitDataDefinitions name s
    case s of
      -- Sorts that admit data definitions.
      Univ _ _     -> yes
      Inf _ _      -> yes
      DefS _ _     -> yes
      -- Sorts that do not admit data definitions.
      SizeUniv     -> no
      LockUniv     -> no
      LevelUniv    -> no
      IntervalUniv -> no
      -- Blocked sorts.
      PiSort _ _ _ -> __IMPOSSIBLE__
      FunSort _ _  -> __IMPOSSIBLE__
      UnivSort _   -> __IMPOSSIBLE__
      MetaS _ _    -> __IMPOSSIBLE__
      DummyS _     -> __IMPOSSIBLE__
  where
    postpone :: Blocker -> Sort -> TCM ()
    postpone b s = addConstraint b $ CheckDataSort name s

-- | Ensure that the type is a sort.
--   If it is not directly a sort, compare it to a 'newSortMetaBelowInf'.
forceSort :: Type -> TCM Sort
forceSort t = reduce (unEl t) >>= \case
  Sort s -> return s
  _      -> do
    s <- newSortMetaBelowInf
    equalType t (sort s)
    return s

-- | Type check a constructor declaration. Checks that the constructor targets
--   the datatype and that it fits inside the declared sort.
--   Returns the non-linear parameters.
checkConstructor
  :: QName         -- ^ Name of data type.
  -> UniverseCheck -- ^ Check universes?
  -> Telescope     -- ^ Parameter telescope.
  -> Nat           -- ^ Number of indices of the data type.
  -> Sort          -- ^ Sort of the data type.
  -> A.Constructor -- ^ Constructor declaration (type signature).
  -> TCM IsPathCons
checkConstructor d uc tel nofIxs s (A.ScopedDecl scope [con]) = do
  setScope scope
  checkConstructor d uc tel nofIxs s con
checkConstructor d uc tel nofIxs s con@(A.Axiom _ i ai Nothing c e) =
    traceCall (CheckConstructor d tel s con) $ do
{- WRONG
      -- Andreas, 2011-04-26: the following happens to the right of ':'
      -- we may use irrelevant arguments in a non-strict way in types
      t' <- workOnTypes $ do
-}
        debugEnter c e
        -- Remember that we are of a suitable modality.
        unless (isRelevant ai) __IMPOSSIBLE__
        unless ((isQuantityω || isQuantity0) ai) __IMPOSSIBLE__

        -- If the constructor is erased, then hard compile-time mode
        -- is entered.
        setHardCompileTimeModeIfErased' ai $ do

        -- check that the type of the constructor is well-formed
        (t, isPathCons) <- checkConstructorType e d

        -- compute which constructor arguments are forced (only point constructors)
        forcedArgs <- if isPathCons == PointCons
                      then computeForcingAnnotations c t
                      else return []
        -- check that the sort (universe level) of the constructor type
        -- is contained in the sort of the data type
        -- (to avoid impredicative existential types)
        debugFitsIn s
        -- To allow propositional squash, we turn @Prop ℓ@ into @Set ℓ@
        -- for the purpose of checking the type of the constructors.
        let s' = case s of
              Prop l -> Type l
              _      -> s
        arity <- applyQuantityToJudgement ai $
          fitsIn c uc forcedArgs t s'
        -- this may have instantiated some metas in s, so we reduce
        s <- reduce s
        debugAdd c t

        (TelV fields _, boundary) <- telViewUpToPathBoundaryP (-1) t

        -- We assume that the current context matches the parameters
        -- of the datatype in an empty context (c.f. getContextSize above).
        params <- getContextTelescope

        (con, comp, projNames) <- do
            -- Name for projection of ith field of constructor c is just c-i
            names <- forM [0 .. size fields - 1] $ \ i ->
              freshAbstractQName'_ $ P.prettyShow (A.qnameName c) ++ "-" ++ show i

            -- nofIxs == 0 means the data type can be reconstructed
            -- by appling the QName d to the parameters.
            let dataT = El s $ Def d $ map Apply $ teleArgs params

            reportSDoc "tc.data.con.comp" 5 $ inTopContext $ vcat $
              [ "params =" <+> pretty params
              , "dataT  =" <+> pretty dataT
              , "fields =" <+> pretty fields
              , "names  =" <+> pretty names
              ]

            let con = ConHead c IsData Inductive $ zipWith (<$) names $ map argFromDom $ telToList fields

            defineProjections d con params names fields dataT
            -- Andreas, 2024-01-05 issue #7048:
            -- Only define hcomp when --cubical-compatible.
            cubicalCompatible <- cubicalCompatibleOption
            -- Cannot compose indexed inductive types yet.
            comp <- if cubicalCompatible && nofIxs == 0 && Info.defAbstract i == ConcreteDef
                    then inTopContext $ defineCompData d con params names fields dataT boundary
                    else return emptyCompKit
            return (con, comp, Just names)

        -- add parameters to constructor type and put into signature
        escapeContext impossible (size tel) $ do
          erasure <- optErasure <$> pragmaOptions
          addConstant' c ai (telePi tel t) $ Constructor
              { conPars   = size tel
              , conArity  = arity
              , conSrcCon = con
              , conData   = d
              , conAbstr  = Info.defAbstract i
              , conComp   = comp
              , conProj   = projNames
              , conForced = forcedArgs
              , conErased = Nothing  -- computed during compilation to treeless
              , conErasure = erasure
              , conInline  = False
              }

        -- Add the constructor to the instance table, if needed
        case Info.defInstance i of
          InstanceDef _r -> setCurrentRange c $ do
            -- Including the range of the @instance@ keyword, like
            -- @(getRange (r,c))@, does not produce good results.
            -- Andreas, 2020-01-28, issue #4360:
            -- Use addTypedInstance instead of addNamedInstance
            -- to detect unusable instances.
            addTypedInstance c t
            -- addNamedInstance c d
          NotInstanceDef -> pure ()

        return isPathCons

  where
    -- Issue 3362: we need to do the `constructs` call inside the
    -- generalization, so unpack the A.Generalize
    checkConstructorType (A.ScopedExpr s e) d = withScope_ s $ checkConstructorType e d
    checkConstructorType e d = do
      let check k e = do
            t <- workOnTypes $ isType_ e
            -- check that the type of the constructor ends in the data type
            n <- getContextSize
            debugEndsIn t d (n - k)
            isPathCons <- constructs (n - k) k t d
            return (t, isPathCons)

      case e of
        A.Generalized s e -> do
          (_, t, isPathCons) <- generalizeType' (Set1.toSet s) (check 1 e)
          return (t, isPathCons)
        _ -> check 0 e

    debugEnter c e =
      reportSDoc "tc.data.con" 5 $ vcat
        [ "checking constructor" <+> prettyTCM c <+> ":" <+> prettyTCM e
        ]
    debugEndsIn t d n =
      reportSDoc "tc.data.con" 15 $ vcat
        [ sep [ "checking that"
              , nest 2 $ prettyTCM t
              , "ends in" <+> prettyTCM d
              ]
        , nest 2 $ "nofPars =" <+> text (show n)
        ]
    debugFitsIn s =
      reportSDoc "tc.data.con" 15 $ sep
        [ "checking that the type fits in"
        , nest 2 $ prettyTCM s
        ]
    debugAdd c t =
      reportSDoc "tc.data.con" 5 $ vcat
        [ "adding constructor" <+> prettyTCM c <+> ":" <+> prettyTCM t
        ]
checkConstructor _ _ _ _ _ _ = __IMPOSSIBLE__ -- constructors are axioms

defineCompData :: QName      -- datatype name
               -> ConHead
               -> Telescope  -- Γ parameters
               -> [QName]    -- projection names
               -> Telescope  -- Γ ⊢ Φ field types
               -> Type       -- Γ ⊢ T target type
               -> Boundary   -- [(i,t_i,b_i)],  Γ.Φ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : B_i
               -> TCM CompKit
defineCompData d con params names fsT t boundary = do
  required <- mapM getTerm'
    [ someBuiltin builtinInterval
    , someBuiltin builtinIZero
    , someBuiltin builtinIOne
    , someBuiltin builtinIMin
    , someBuiltin builtinIMax
    , someBuiltin builtinINeg
    , someBuiltin builtinPOr
    , someBuiltin builtinItIsOne
    ]
  if not (all isJust required) then return $ emptyCompKit else do
    hcomp  <- whenDefined (null boundary) [builtinHComp,builtinTrans]
      (defineKanOperationD DoHComp  d con params names fsT t boundary)
    transp <- whenDefined True            [builtinTrans]
      (defineKanOperationD DoTransp d con params names fsT t boundary)
    return $ CompKit
      { nameOfTransp = transp
      , nameOfHComp  = hcomp
      }
  where
    -- Δ^I, i : I |- sub Δ : Δ
    sub tel = [ var n `apply` [Arg defaultArgInfo $ var 0] | n <- [1..size tel] ] ++# EmptyS __IMPOSSIBLE__
    withArgInfo tel = zipWith Arg (map domInfo . telToList $ tel)

    defineKanOperationD cmd d con params names fsT t boundary = do
      let project = (\ t p -> apply (Def p []) [argN t])
      stuff <- defineKanOperationForFields cmd
                 (guard (not $ null boundary) >> Just (Con con ConOSystem $ teleElims fsT boundary))
                 project d params fsT (map argN names) t
      caseMaybe stuff (return Nothing) $ \ ((theName, gamma , ty, _cl_types , bodies), theSub) -> do

      iz <- primIZero
      body <- do
        case cmd of
          DoHComp -> return $ Con con ConOSystem (map Apply $ withArgInfo fsT bodies)
          DoTransp | null boundary {- && null ixs -} -> return $ Con con ConOSystem (map Apply $ withArgInfo fsT bodies)
                   | otherwise -> do
            io <- primIOne
            tIMax <- primIMax
            tIMin <- primIMin
            tINeg <- primINeg
            tPOr  <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
            tHComp <- primHComp
            -- Δ = params
            -- Δ ⊢ Φ = fsT
            -- (δ : Δ) ⊢ T = R δ
            -- (δ : Δ) ⊢ con : Φ → R δ  -- no indexing
            -- boundary = [(i,t_i,u_i)]
            -- Δ.Φ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : B_i
            -- Δ.Φ | PiPath Φ boundary (R δ) |- teleElims fsT boundary : R δ
            -- Γ = ((δ : Δ^I), φ, us : Φ[δ 0]) = gamma
            -- Γ ⊢ ty = R (δ i1)
            -- (γ : Γ) ⊢ cl_types = (flatten Φ)[n ↦ f_n (transpR γ)]
            -- Γ ⊢ bodies : Φ[δ i1]
            -- Γ ⊢ t : ty
            -- Γ, i : I ⊢ theSub : Δ.Φ
            let

              -- Δ.Φ ⊢ u = Con con ConOSystem $ teleElims fsT boundary : R δ
              u = Con con ConOSystem $ teleElims fsT boundary
              -- Γ ⊢ u
              the_u = liftS (size fsT) d0 `applySubst` u
                where
                  -- δ : Δ^I, φ : F ⊢ [δ 0] : Δ
                  d0 :: Substitution
                  d0 = wkS 1 -- Δ^I, φ : F ⊢ Δ
                             (consS iz IdS `composeS` sub params) -- Δ^I ⊢ Δ
                                       -- Δ^I , i:I ⊢ sub params : Δ
              the_phi = raise (size fsT) $ var 0
              -- Γ ⊢ sigma : Δ.Φ
              -- sigma = [δ i1,bodies]
              -- sigma = theSub[i1]
              sigma = reverse bodies ++# d1
               where
                -- δ i1
                d1 :: Substitution
                d1 = wkS (size gamma - size params) -- Γ ⊢ Δ
                       (consS io IdS `composeS` sub params) -- Δ^I ⊢ Δ
                                 -- Δ^I , i:I ⊢ sub params : Δ

              -- Δ.Φ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : R δ
              bs = fullBoundary fsT boundary
              -- ψ = sigma `applySubst` map (\ i → i ∨ ~ i) . map fst $ boundary
              -- Γ ⊢ t : R (δ i1)
              w1' = Con con ConOSystem $ sigma `applySubst` teleElims fsT boundary
              -- (δ, φ, u0) : Γ ⊢
              -- w1 = hcomp (\ i → R (δ i1))
              --            (\ i → [ ψ ↦ α (~ i), φ ↦ u0])
              --            w1'
              imax x y = pure tIMax <@> x <@> y
              ineg r = pure tINeg <@> r
              lvlOfType = (\ (Type l) -> Level l) . getSort
              pOr la i j u0 u1 = pure tPOr <#> (lvlOfType <$> la) <@> i <@> j
                                           <#> ilam "o" (\ _ -> unEl <$> la) <@> u0 <@> u1
              absAp x y = liftM2 absApp x y

              mkFace (r,(u1,u2)) = runNamesT [] $ do
                -- Γ
                phi <- open the_phi  -- (δ , φ , us) ⊢ φ
                -- Γ ⊢ ty = Abs i. R (δ i)
                ty <- open (Abs "i" $ (liftS 1 (raiseS (size gamma - size params)) `composeS` sub params) `applySubst` t)

                bind "i" $ \ i -> do
                  -- Γ, i
                  r  <- open . applySubst theSub $ r
                  u1 <- open . applySubst theSub $ u1
                  u2 <- open . applySubst theSub $ u2
                  psi <- imax r (ineg r)
                  let
                    -- Γ, i ⊢ squeeze u = primTrans (\ j -> ty [i := i ∨ j]) (φ ∨ i) u
                    squeeze u = cl primTrans
                                          <#> lam "j" (\ j -> lvlOfType <$> ty `absAp` (imax i j))
                                          <@> lam "j" (\ j -> unEl <$> ty `absAp` (imax i j))
                                          <@> (phi `imax` i)
                                          <@> u
                  alpha <- pOr (ty `absAp` i)
                              (ineg r)
                              r
                           (ilam "o" $ \ _ -> squeeze u1) (ilam "o" $ \ _ -> squeeze u2)
                  return $ (psi, alpha)

            -- Γ ⊢ Abs i. [(ψ_n,α_n : [ψ] → R (δ i))]
            faces <- mapM mkFace bs

            runNamesT [] $ do
                -- Γ
                w1' <- open w1'
                phi <- open the_phi
                u   <- open the_u
                -- R (δ i1)
                ty <- open ty
                faces <- mapM (\ x -> liftM2 (,) (open . noabsApp __IMPOSSIBLE__ $ fmap fst x) (open $ fmap snd x)) faces
                let
                  thePsi = foldl1 imax (map fst faces)
                  hcomp ty phi sys a0 = pure tHComp <#> (lvlOfType <$> ty)
                                                    <#> (unEl <$> ty)
                                                    <#> phi
                                                    <@> sys
                                                    <@> a0
                let
                 sys = lam "i" $ \ i -> do
                  let
                    recurse [(psi,alpha)] = alpha `absAp` (ineg i)
                    recurse ((psi,alpha):xs) = pOr ty
                                                   psi  theOr
                                                   (alpha `absAp` (ineg i)) (recurse xs)
                      where
                        theOr = foldl1 imax (map fst xs)
                    recurse [] = __IMPOSSIBLE__
                    sys_alpha = recurse faces
                  pOr ty
                                                   thePsi    phi
                                                   sys_alpha (ilam "o" $ \ _ -> u)
                hcomp ty (thePsi `imax` phi) sys w1'


      let

        -- δ : Δ^I, φ : F ⊢ [δ 0] : Δ
        d0 :: Substitution
        d0 = wkS 1 -- Δ^I, φ : F ⊢ Δ
                       (consS iz IdS `composeS` sub params) -- Δ^I ⊢ Δ
                                 -- Δ^I , i:I ⊢ sub params : Δ

        -- Δ.Φ ⊢ u = Con con ConOSystem $ teleElims fsT boundary : R δ
--        u = Con con ConOSystem $ teleElims fsT boundary
        up = ConP con (ConPatternInfo defaultPatternInfo False False Nothing False) $
               telePatterns (d0 `applySubst` fsT) (liftS (size fsT) d0 `applySubst` boundary)
--        gamma' = telFromList $ take (size gamma - 1) $ telToList gamma

        -- (δ , φ , fs : Φ[d0]) ⊢ u[liftS Φ d0]
        -- (δ , φ, u) : Γ ⊢ body
        -- Δ ⊢ Φ = fsT
        -- (δ , φ , fs : Φ[d0]) ⊢ u[liftS Φ d0] `consS` raiseS Φ : Γ
--        (tel',theta) = (abstract gamma' (d0 `applySubst` fsT), (liftS (size fsT) d0 `applySubst` u) `consS` raiseS (size fsT))

      let
        pats | null boundary = teleNamedArgs gamma
             | otherwise     = take (size gamma - size fsT) (teleNamedArgs gamma) ++ [argN $ unnamed $ up]
        clause = Clause
          { clauseTel         = gamma
          , clauseType        = Just . argN $ ty
          , namedClausePats   = pats
          , clauseFullRange   = noRange
          , clauseLHSRange    = noRange
          , clauseCatchall    = False
          , clauseBody        = Just $ body
          , clauseRecursive   = Nothing
              -- Andreas 2020-02-06 TODO
              -- Or: Just False;  is it known to be non-recursive?
          , clauseUnreachable = Just False
          , clauseEllipsis    = NoEllipsis
          , clauseWhereModule = Nothing
          }
        cs = [clause]
      addClauses theName cs
      (mst, _, cc) <- inTopContext (compileClauses Nothing cs)
      whenJust mst $ setSplitTree theName
      setCompiledClauses theName cc
      setTerminates theName True
      return $ Just theName

    whenDefined False _ _ = return Nothing
    whenDefined True xs m = do
      xs <- mapM getTerm' xs
      if all isJust xs then m else return Nothing

-- Andrea: TODO handle Irrelevant fields somehow.
-- | Define projections for non-indexed data types (families don't work yet).
--   Of course, these projections are partial functions in general.
--
--   Precondition: we are in the context Γ of the data type parameters.
defineProjections :: QName      -- datatype name
                  -> ConHead
                  -> Telescope  -- Γ parameters
                  -> [QName]    -- projection names
                  -> Telescope  -- Γ ⊢ Φ field types
                  -> Type       -- Γ ⊢ T target type
                  -> TCM ()
defineProjections dataName con params names fsT t = do
  let
    -- Γ , (d : T) ⊢ Φ[n ↦ proj n d]
    fieldTypes = ([ Def f [] `apply` [argN $ var 0] | f <- reverse names ] ++# raiseS 1) `applySubst`
                    flattenTel fsT  -- Γ , Φ ⊢ Φ
    -- ⊢ Γ , (d : T)
    projTel    = abstract params (ExtendTel (defaultDom t) (Abs "d" EmptyTel))
    np         = size params

  forM_ (zip3 (downFrom (size fieldTypes)) names fieldTypes) $ \ (i,projName,ty) -> do
    let
      projType = abstract projTel <$> ty
      cpi    = ConPatternInfo defaultPatternInfo False False (Just $ argN $ raise (size fsT) t) False
      conp   = defaultNamedArg $ ConP con cpi $ teleNamedArgs fsT
      sigma  = Con con ConOSystem (map Apply $ teleArgs fsT) `consS` raiseS (size fsT)
      clause = empty
          { clauseTel         = abstract params fsT
          , namedClausePats   = [ conp ]
          , clauseBody        = Just $ var i
          , clauseType        = Just $ argN $ applySubst sigma $ unDom ty
          , clauseRecursive   = Just False  -- non-recursive
          , clauseUnreachable = Just False
          }

    reportSDoc "tc.data.proj" 20 $ inTopContext $ sep
      [ "proj" <+> prettyTCM (i,ty)
      , nest 2 $ sep [ prettyTCM projName, ":", prettyTCM projType ]
      ]

    -- Andreas, 2020-02-14, issue #4437
    -- Define data projections as projection-like from the start.
    noMutualBlock $ do
      let cs = [ clause ]
      (mst, _, cc) <- compileClauses Nothing cs
      fun          <- emptyFunctionData <&> \fun -> fun
                { _funClauses    = cs
                , _funCompiled   = Just cc
                , _funSplitTree  = mst
                , _funProjection = Right Projection
                    { projProper   = Nothing
                    , projOrig     = projName
                    , projFromType = Arg (getArgInfo ty) dataName
                    , projIndex    = np + 1
                    , projLams     = ProjLams $ map (argFromDom . fmap fst) $ telToList projTel
                    }
                , _funMutual     = Just []
                , _funTerminates = Just True
                }
      lang <- getLanguage
      inTopContext $ addConstant projName $
        (defaultDefn defaultArgInfo projName (unDom projType) lang $ FunctionDefn fun)
          { defNoCompilation  = True
          , defArgOccurrences = [StrictPos]
          }

      reportSDoc "tc.data.proj.fun" 60 $ inTopContext $ vcat
        [ "proj" <+> prettyTCM i
        , nest 2 $ pretty fun
        ]


freshAbstractQName'_ :: String -> TCM QName
freshAbstractQName'_ = freshAbstractQName noFixity' . C.simpleName


-- | Defines and returns the name of the `transpIx` function.
defineTranspIx :: QName  -- ^ datatype name
               -> TCM (Maybe QName)
defineTranspIx d = do
  def <- getConstInfo d
  case theDef def of
    Datatype { dataPars = npars
             , dataIxs = nixs
             , dataSort = s}
     -> do
      let t = defType def
      reportSDoc "tc.data.ixs" 20 $ vcat
        [ "name :" <+> prettyTCM d
        , "type :" <+> prettyTCM t
        , "npars:" <+> pretty npars
        , "nixs :" <+> pretty nixs
        ]
      if nixs == 0 then return Nothing else do
      trIx <- freshAbstractQName'_ $ "transpX-" ++ P.prettyShow (A.qnameName d)
      TelV params t' <- telViewUpTo npars t
      TelV ixs    dT <- telViewUpTo nixs t'
      -- params     ⊢ s
      -- params     ⊢ ixs
      -- params.ixs ⊢ dT
      reportSDoc "tc.data.ixs" 20 $ vcat
        [ "params :" <+> prettyTCM params
        , "ixs    :" <+> addContext params (prettyTCM ixs)
        , "dT     :" <+> addContext params (addContext ixs $ prettyTCM dT)
        ]
      -- theType <- abstract params <$> undefined
      interval <- primIntervalType
      let deltaI = expTelescope interval ixs
      iz <- primIZero
      io@(Con c _ _) <- primIOne
      imin <- getPrimitiveTerm builtinIMin
      imax <- getPrimitiveTerm builtinIMax
      ineg <- getPrimitiveTerm builtinINeg
      transp <- getPrimitiveTerm builtinTrans
      por <- getPrimitiveTerm builtinPOr
      one <- primItIsOne
      -- reportSDoc "trans.rec" 20 $ text $ show params
      -- reportSDoc "trans.rec" 20 $ text $ show deltaI
      -- reportSDoc "trans.rec" 10 $ text $ show fsT

      -- let thePrefix = "transp-"
      -- theName <- freshAbstractQName'_ $ thePrefix ++ P.prettyShow (A.qnameName name)

      -- reportSLn "trans.rec" 5 $ ("Generated name: " ++ show theName ++ " " ++ showQNameId theName)

      -- record type in 'exponentiated' context
      -- (params : Γ)(ixs : Δ^I), i : I |- T[params, ixs i]
      let rect' = sub ixs `applySubst` El (raise (size ixs) s) (Def d (teleElims (abstract params ixs) []))
      addContext params $ reportSDoc "tc.data.ixs" 20 $ "deltaI:" <+> prettyTCM deltaI
      addContext params $ addContext deltaI $ addContext ("i"::String, defaultDom interval) $ do
        reportSDoc "tc.data.ixs" 20 $ "rect':" <+> pretty (sub ixs)
        reportSDoc "tc.data.ixs" 20 $ "rect':" <+> pretty rect'

      theType <- (abstract (setHiding Hidden <$> params) <$>) . (abstract deltaI <$>) $ runNamesT [] $ do
                  rect' <- open (runNames [] $ bind "i" $ \ x -> let _ = x `asTypeOf` pure (undefined :: Term) in
                                                                 pure rect')
                  nPi' "phi" (primIntervalType) $ \ phi ->
                   (absApp <$> rect' <*> pure iz) --> (absApp <$> rect' <*> pure io)

      reportSDoc "tc.data.ixs" 20 $ "transpIx:" <+> prettyTCM theType
      let
        ctel = abstract params $ abstract deltaI $ ExtendTel (defaultDom $ subst 0 iz rect') (Abs "t" EmptyTel)
        ps = telePatterns ctel []
        cpi = noConPatternInfo { conPType = Just (defaultArg interval) }
        pat :: NamedArg (Pattern' DBPatVar)
        pat = defaultNamedArg $ ConP c cpi []
        clause = empty
          { clauseTel         = ctel
          , namedClausePats   = init ps ++ [pat, last ps]

          , clauseBody        = Just $ var 0
          , clauseType        = Just $ defaultArg $ raise 1 $ subst 0 io rect'
          , clauseRecursive   = Just False  -- non-recursive
          , clauseUnreachable = Just False
          }

      noMutualBlock $ do
        let cs = [ clause ]
--        we do not compile clauses as that leads to throwing missing clauses errors.
--        (mst, _, cc) <- compileClauses Nothing cs
        fun <- emptyFunctionData <&> \fun -> fun
                  { _funClauses    = cs
               --   , _funCompiled   = Just cc
               --   , _funSplitTree  = mst
                  , _funProjection = Left MaybeProjection
                  , _funMutual     = Just []
                  , _funTerminates = Just True
                  , _funIsKanOp    = Just d
                  }
        inTopContext $ do
         reportSDoc "tc.transpx.type" 15 $ vcat
           [ "type of" <+> prettyTCM trIx <+> ":"
           , nest 2 $ prettyTCM theType
           ]

         addConstant trIx $
          (defaultDefn defaultArgInfo trIx theType (Cubical CErased) $ FunctionDefn fun)
            { defNoCompilation  = True
            }

        -- reportSDoc "tc.data.proj.fun" 60 $ inTopContext $ vcat
        --   [ "proj" <+> prettyTCM i
        --   , nest 2 $ pretty fun
        --   ]
      -- addContext ctel $ do
      --   let es = teleElims ctel []
      --   r <- reduce $ Def trIx es
      --   reportSDoc "tc.data.ixs" 20 $ "reducedx:" <+> prettyTCM r
      --   r <- reduce $ Def trIx (init es ++ [Apply $ argN io, last es])
      --   reportSDoc "tc.data.ixs" 20 $ "reduced1:" <+> prettyTCM r
      return $ Just trIx
    _ -> __IMPOSSIBLE__
  where

    -- Γ, Δ^I, i : I |- sub (Γ ⊢ Δ) : Γ, Δ
    sub tel = expS $ size tel


defineTranspFun :: QName -- ^ datatype
                -> Maybe QName -- ^ transpX "constructor"
                -> [QName]     -- ^ constructor names
                -> [QName]     -- ^ path cons
                -> TCM (Maybe QName) -- transp function for the datatype.
defineTranspFun d mtrX cons pathCons = do
  def <- getConstInfo d
  case theDef def of
    Datatype { dataPars = npars
             , dataIxs = nixs
             , dataSort = s@(Type _)
--             , dataCons = cons -- not there yet
             }
     -> do
      let t = defType def
      reportSDoc "tc.data.transp" 20 $ vcat
        [ "name :" <+> prettyTCM d
        , "type :" <+> prettyTCM t
        , "npars:" <+> pretty npars
        , "nixs :" <+> pretty nixs
        ]
      trD <- freshAbstractQName'_ $ "transp" ++ P.prettyShow (A.qnameName d)
      TelV params t' <- telViewUpTo npars t
      TelV ixs    dT <- telViewUpTo nixs t'

      let tel = abstract params ixs
      mixs <- runMaybeT $ traverse (traverse (MaybeT . toLType)) ixs
      caseMaybe mixs (return Nothing) $ \ _ -> do

      io@(Con io_c _ []) <- primIOne
      iz <- primIZero

      interval <- primIntervalType
      let telI = expTelescope interval tel
          sigma = sub tel
          dTs = (sigma `applySubst` El s (Def d $ map Apply $ teleArgs tel))

      theType <- (abstract telI <$>) $ runNamesT [] $ do
                  dT <- open $ Abs "i" $ dTs
                  nPi' "phi" primIntervalType $ \ phi ->
                   (absApp <$> dT <*> pure iz) --> (absApp <$> dT <*> pure io)


      reportSDoc "tc.data.transp" 20 $ "transpD:" <+> prettyTCM theType


      noMutualBlock $ do
        fun <- emptyFunction
        inTopContext $ addConstant trD $
          (defaultDefn defaultArgInfo trD theType (Cubical CErased) fun)
        let
          ctel = abstract telI $ ExtendTel (defaultDom $ subst 0 iz dTs) (Abs "t" EmptyTel)
          ps = telePatterns ctel []
          cpi = noConPatternInfo { conPType = Just (defaultArg interval)
                                 , conPFallThrough = True
                                 }
          pat :: NamedArg (Pattern' DBPatVar)
          pat = defaultNamedArg $ ConP io_c cpi []
          clause = empty
            { clauseTel         = ctel
            , namedClausePats   = init ps ++ [pat, last ps]

            , clauseBody        = Just $ var 0
            , clauseType        = Just $ defaultArg $ raise 1 $ subst 0 io dTs
            , clauseRecursive   = Just False  -- non-recursive
            , clauseUnreachable = Just False
            }
        let debugNoTransp cl = enterClosure cl $ \ t -> do
              reportSDoc "tc.data.transp" 20 $ addContext ("i" :: String, __DUMMY_DOM__) $
                "could not transp" <+> prettyTCM (absBody t)
        -- TODO: if no params nor indexes trD phi u0 = u0.
        ecs <- tryTranspError $ (clause:) <$> defineConClause trD (not $ null pathCons) mtrX npars nixs ixs telI sigma dTs cons
        caseEitherM (pure ecs) (\ cl -> debugNoTransp cl >> return Nothing) $ \ cs -> do
        (mst, _, cc) <- compileClauses Nothing cs
        fun <- emptyFunctionData <&> \fun -> fun
                  { _funClauses    = cs
                  , _funCompiled   = Just cc
                  , _funSplitTree  = mst
                  , _funProjection = Left MaybeProjection
                  , _funMutual     = Just []
                  , _funTerminates = Just True
                  , _funIsKanOp    = Just d
                  }
        inTopContext $ addConstant trD $
          (defaultDefn defaultArgInfo trD theType (Cubical CErased) $ FunctionDefn fun)
            { defNoCompilation  = True
            }
        reportSDoc "tc.data.transp" 20 $ sep
          [ "transp: compiled clauses of " <+> prettyTCM trD
          , nest 2 $ return $ P.pretty cc
          ]

        return $ Just trD


    Datatype {} -> return Nothing
    _           -> __IMPOSSIBLE__
  where
    -- Γ, Δ^I, i : I |- sub (Γ ⊢ Δ) : Γ, Δ
    sub tel = expS (size tel)

defineConClause :: QName -- ^ trD
                -> Bool  -- ^ HIT
                -> Maybe QName -- ^ trX
                -> Nat  -- ^ npars = size Δ
                -> Nat  -- ^ nixs = size X
                -> Telescope -- ^ Δ ⊢ X
                -> Telescope -- ^ (Δ.X)^I
                -> Substitution -- ^ (Δ.X)^I, i : I ⊢ σ : Δ.X
                -> Type       -- ^ (Δ.X)^I, i : I ⊢ D[δ i,x i] -- datatype
                -> [QName]      -- ^ Constructors
                -> TCM [Clause]
defineConClause trD' isHIT mtrX npars nixs xTel' telI sigma dT' cnames = do

  unless (isNothing mtrX == (nixs == 0)) $ __IMPOSSIBLE__

  io <- primIOne
  iz <- primIZero
  tHComp <- primHComp
  tINeg <- primINeg
  let max i j = cl primIMax <@> i <@> j
  let min i j = cl primIMin <@> i <@> j
  let neg i = cl primINeg <@> i
  let hcomp ty sys u0 = do
          ty <- ty
          LEl l ty <- fromMaybe __IMPOSSIBLE__ <$> toLType ty
          l <- open $ Level l
          ty <- open $ ty
          face <- (foldr max (pure iz) $ map fst $ sys)
          sys <- lam "i'" $ \ i -> combineSys l ty [(phi, u <@> i) | (phi,u) <- sys]
          pure tHComp <#> l <#> ty <#> pure face <@> pure sys <@> u0
  interval <- primIntervalType
  let intervalTel nm = ExtendTel (defaultDom interval) (Abs nm EmptyTel)

  let (parI,ixsI) = splitTelescopeAt npars telI
  let
    abstract_trD :: Monad m => (Vars m -> Vars m -> Vars m -> NamesT m Telescope) -> NamesT m Telescope
    abstract_trD k = do
               ixsI <- open $ AbsN (teleNames parI) ixsI
               parI <- open parI
               abstractN parI $ \ delta -> do
               abstractN (ixsI `applyN` delta) $ \ x -> do
               abstractN (pure $ intervalTel "phi") $ \ phi -> do
               k delta x phi
    bind_trD :: Monad m => (ArgVars m -> ArgVars m -> ArgVars m -> NamesT m b) ->
                NamesT m (AbsN (AbsN (AbsN b)))
    bind_trD k = do
      bindNArg (teleArgNames parI) $ \ delta_ps -> do
      bindNArg (teleArgNames ixsI) $ \ x_ps -> do
      bindNArg (teleArgNames $ intervalTel "phi") $ \ phi_ps -> do
      k delta_ps x_ps phi_ps
  let trD = bindNArg (teleArgNames parI) $ \ delta ->
            bindNArg (teleArgNames ixsI) $ \ x ->
            bindN ["phi","u0"]           $ \ [phi,u0] ->
              ((Def trD' [] `apply`) <$> sequence (delta ++ x)) <@> phi <@> u0
  -- [Δ] ⊢ X
  let xTel = pure $ AbsN (teleNames parI) xTel'
  -- [δ : Δ^I, x : X^I, i : I] ⊢ D (δ i) (x i)
  let dT = pure $ AbsN (teleNames parI ++ teleNames ixsI ++ ["i"]) dT'

  let hcompComputes = not $ isHIT || nixs > 0
  c_HComp <- if hcompComputes then return [] else do
      reportSDoc "tc.data.transp.con" 20 $ "======================="
      reportSDoc "tc.data.transp.con" 20 $ "hcomp"
      qHComp <- fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' builtinHComp
      hcomp_ty <- defType <$> getConstInfo qHComp
      gamma <- runNamesT [] $ do
               ixsI <- open $ AbsN (teleNames parI) ixsI
               parI <- open parI
               abstract_trD $ \ delta x _ -> do
               LEl l ty <- fromMaybe __IMPOSSIBLE__ <.> toLType =<< (dT `applyN` (delta ++ x ++ [pure iz]))
               -- (φ : I), (I → Partial φ (D (δ i0) (x i0))), D (δ i0) (x i0)
               TelV args _ <- lift $ telView =<< piApplyM hcomp_ty [Level l,ty]
               unless (size args == 3) __IMPOSSIBLE__
               pure args
      res <- runNamesT [] $ do
        let hcompArgs = map argN ["phi","u","u0"]
        bind_trD $ \ delta_ps x_ps phi_ps -> do
        let x = map (fmap unArg) x_ps
        let delta = map (fmap unArg) delta_ps
        let [phi] = map (fmap unArg) phi_ps
        bindNArg hcompArgs $ \ as0 -> do -- as0 : aTel[delta 0]
        let
          origPHComp = do
            LEl l t <- fromMaybe __IMPOSSIBLE__ <.> toLType =<< (dT `applyN` (delta ++ x ++ [pure iz]))
            let ds = map (argH . unnamed . dotP) [Level l, t]
            sequence as0 >>= \case
              ps0@[_hphi,_u,_u0] ->
                pure $ DefP defaultPatternInfo qHComp $ ds ++ ps0
              _ -> __IMPOSSIBLE__
          psHComp = sequence $ delta_ps ++ x_ps ++ phi_ps ++ [argN . unnamed <$> origPHComp]
        let
          rhsTy = dT `applyN` (delta ++ x ++ [pure io])
        -- trD δ x φ (hcomp [hφ ↦ u] u0) ↦ rhsHComp
        let rhsHComp = do
              let [hphi,u,u0] = map (fmap unArg) as0
              -- TODO: should trD be transp for the datatype?
              let baseHComp = trD `applyN` delta `applyN` x `applyN` [phi,u0]
              let sideHComp = lam "i" $ \ i -> ilam "o" $ \ o -> do
                     trD `applyN` delta `applyN` x `applyN` [phi,u <@> i <..> o]
              hcomp rhsTy [(hphi, sideHComp)] baseHComp
        (,,) <$> psHComp <*> rhsTy <*> rhsHComp
      let (ps,rhsTy,rhs) = unAbsN $ unAbsN $ unAbsN $ unAbsN $ res
      (:[]) <$> mkClause gamma ps rhsTy rhs


  c_trX   <- caseMaybe mtrX (pure []) $ \ trX -> do
        reportSDoc "tc.data.transp.con" 20 $ "======================="
        reportSDoc "tc.data.transp.con" 20 $ prettyTCM trX
        gamma <- runNamesT [] $ do
                     ixsI <- open $ AbsN (teleNames parI) ixsI
                     parI <- open parI
                     abstract_trD $ \ delta _ _ -> do
                     let delta0_refl = for delta $ \ p -> lam "i" $ \ _ -> p <@> pure iz
                     abstractN (ixsI `applyN` delta0_refl) $ \ x' -> do
                     abstractN (pure $ intervalTel "phi'") $ \ _ -> do
                     ty <- dT `applyN` (delta0_refl ++ x' ++ [pure iz])
                     pure $ ExtendTel (defaultDom ty) $ Abs "t" EmptyTel
        res <- runNamesT [] $
          bind_trD $ \ delta_ps x_ps phi_ps -> do
          let x = map (fmap unArg) x_ps
          let delta = map (fmap unArg) delta_ps
          let [phi] = map (fmap unArg) phi_ps
          --- pattern matching args below
          bindNArg (map (fmap (++ "'")) (teleArgNames ixsI)) $ \ x'_ps -> do
          let x' = map (fmap unArg) x'_ps :: [NamesT TCM Term]
          let phi'name = teleArgNames $ intervalTel "phi'"
          bindNArg phi'name $ \ phi'_ps -> do
          let phi's = map (fmap unArg) phi'_ps
          bindNArg [argN "t"] $ \ as0 -> do
          let deltaArg i = do
                i <- i
                xs <- sequence delta_ps
                pure $ map (fmap (`apply` [argN i])) xs

          let
            origPTrX = do
              x'_ps <- sequence x'_ps
              phi'_ps <- sequence phi'_ps
              ds <- map (setHiding Hidden . fmap (unnamed . dotP)) <$> deltaArg (pure iz)
              ps0 <- sequence as0
              unless (length ps0 == 1) __IMPOSSIBLE__
              pure $ DefP defaultPatternInfo trX $ ds ++ x'_ps ++ phi'_ps ++ ps0
            psTrX = sequence $ delta_ps ++ x_ps ++ phi_ps ++ [argN . unnamed <$> origPTrX]

            rhsTy = dT `applyN` (delta ++ x ++ [pure io])

          -- trD δ x φ (trX x' φ' t) ↦ rhsTrx
          let rhsTrX = do
                let [t] = map (fmap unArg) as0
                let [phi'] = phi's
                let telXdeltai = bind "i" $ \ i -> applyN xTel (map (<@> i) delta)
                let reflx1 = for x $ \ q -> lam "i" $ \ _ -> q <@> pure io
                let symx' = for x' $ \ q' -> lam "i" $ \ i -> q' <@> neg i
                x_tr <- mapM (open . unArg) =<< transpPathTel' telXdeltai symx' reflx1 phi' x
                let baseTrX = trD `applyN` delta `applyN` x_tr `applyN` [phi `min` phi',t]
                let sideTrX = lam "j" $ \ j -> ilam "o" $ \ _ -> do
                      let trD_f = trD `applyN` for delta (\ p -> lam "i" $ \ i -> p <@> (i `min` neg j))
                                      `applyN` for x_tr (\ p -> lam "i" $ \ i -> p <@> (i `min` neg j))
                                      `applyN` [(phi `min` phi') `max` j,t]
                      let x_tr_f = fmap (fmap (\ (Abs n (Arg i t)) -> Arg i $ Lam defaultArgInfo (Abs n t)) . sequence) $
                           bind "i" $ \ i -> do
                            j <- j
                            map (fmap (`apply` [argN j])) <$> trFillPathTel' telXdeltai symx' reflx1 phi' x (neg i)
                      let args = liftM2 (++) (map (setHiding Hidden) <$> deltaArg (pure io)) x_tr_f
                      (apply (Def trX []) <$> args) <@> (phi' `max` neg j) <@> trD_f
                hcomp rhsTy [(phi,sideTrX),(phi',lam "i" $ \ _ -> ilam "o" $ \ _ -> baseTrX)]
                            baseTrX

          (,,) <$> psTrX <*> rhsTy <*> rhsTrX


        let (ps,rhsTy,rhs) = unAbsN $ unAbsN $ unAbsN $ unAbsN $ unAbsN $ unAbsN $ res
        (:[]) <$> mkClause gamma ps rhsTy rhs

  fmap ((c_HComp ++ c_trX) ++) $ forM cnames $ \ cname -> do
    def <- getConstInfo cname
    let
      Constructor
       { conPars = npars'
       , conArity = nargs
       , conSrcCon = chead
       } = theDef def
    do
        let tcon = defType def

        reportSDoc "tc.data.transp.con" 20 $ "======================="
        reportSDoc "tc.data.transp.con" 20 $ "tcon:" <+> prettyTCM (conName chead) <+> prettyTCM tcon

        unless (conName chead == cname && npars' == npars) $ __IMPOSSIBLE__


        TelV prm tcon' <- telViewUpTo npars' tcon
        -- Δ ⊢ aTel
        -- Δ.aTel ⊢ ty
        -- Δ.aTel ⊢ [(φ,(l,r))] = boundary : ty
        (TelV aTel ty, boundary) <- telViewUpToPathBoundary nargs tcon'

        Def _ es <- unEl <$> reduce ty
        -- Δ.aTel ⊢ con_ixs : X
        let con_ixs = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ drop npars es

        reportSDoc "tc.data.transp.con" 20 $
          addContext prm $ "aTel:" <+> prettyTCM aTel
        reportSDoc "tc.data.transp.con" 20 $
          addContext prm $ addContext aTel $ "ty:" <+> prettyTCM ty
        reportSDoc "tc.data.transp.con" 20 $
          addContext prm $ addContext aTel $ "boundary:" <+> prettyTCM boundary

        gamma <- runNamesT [] $ do
                     ixsI <- open $ AbsN (teleNames parI) ixsI
                     aTel <- open $ AbsN (teleNames prm) aTel
                     parI <- open parI
                     abstract_trD $ \ delta _ _ -> do
                     let args = aTel `applyN` map (<@> pure iz) delta
                     args
        res <- runNamesT [] $ do
          let aTelNames = teleNames aTel
              aTelArgs = teleArgNames aTel
          con_ixs <- open $ AbsN (teleNames prm ++ teleNames aTel) $ map unArg con_ixs
          bndry <- open $ AbsN (teleNames prm ++ teleNames aTel) $ boundary
          u    <- open $ AbsN (teleNames prm ++ aTelNames) $ Con chead ConOSystem (teleElims aTel boundary)
          aTel <- open $ AbsN (teleNames prm) aTel
          -- bsys : Abs Δ.Args ([phi] → ty)
          (bsysFace,bsys) <- do
            p <- bindN (teleNames prm ++ aTelNames) $ \ ts -> do
              LEl l ty <- fromMaybe __IMPOSSIBLE__ <$> toLType ty
              l <- open (Level l)
              ty <- open ty
              bs <- bndry `applyN` ts
              xs <- mapM (\(phi,u) -> (,) <$> open phi <*> open u) $ do
                (i,(l,r)) <- bs
                let pElem t = Lam defaultIrrelevantArgInfo $ NoAbs "o" t
                [(tINeg `apply` [argN i],pElem l),(i,pElem r)]
              combineSys' l ty xs
            (,) <$> open (fst <$> p) <*> open (snd <$> p)
          bind_trD $ \ delta_ps x_ps phi_ps -> do
          let x = map (fmap unArg) x_ps
          let delta = map (fmap unArg) delta_ps
          let [phi] = map (fmap unArg) phi_ps
          --- pattern matching args below
          bindNArg aTelArgs $ \ as0 -> do -- as0 : aTel[delta 0]

          let aTel0 = aTel `applyN` map (<@> pure iz) delta

          -- telePatterns is not context invariant, so we need an open here where the context ends in aTel0.
          ps0 <- (open =<<) $ (telePatterns <$> aTel0 <*> applyN bndry (map (<@> pure iz) delta ++ map (fmap unArg) as0))

          let deltaArg i = do
                i <- i
                xs <- sequence delta_ps
                pure $ map (fmap (`apply` [argN i])) xs

          let
            origP = ConP chead noConPatternInfo <$> ps0
            ps = sequence $ delta_ps ++ x_ps ++ phi_ps ++ [argN . unnamed <$> origP]
          let
            orig = patternToTerm <$> origP
            rhsTy = dT `applyN` (delta ++ x ++ [pure io])

          (,,) <$> ps <*> rhsTy <*> do

          -- Declared Constructors.
          let aTelI = bind "i" $ \ i -> aTel `applyN` map (<@> i) delta

          eas1 <- (=<<) (lift . runExceptT) $ transpTel <$> aTelI <*> phi <*> sequence as0

          caseEitherM (pure eas1) (lift . lift . E.throw . CannotTransp) $ \ as1 -> do

          as1 <- mapM (open . unArg) as1

          as01 <- (open =<<) $ bind "i" $ \ i -> do
            eas01 <- (=<<) (lift . runExceptT) $ trFillTel <$> aTelI <*> phi <*> sequence as0 <*> i
            caseEitherM (pure eas01) (lift . lift . E.throw . CannotTransp) pure

          let argApp a t = liftM2 (\ a t -> fmap (`apply` [argN t]) a) a t
          let
            argLam :: Monad m => String -> (Var m -> NamesT m (Arg Term)) -> NamesT m (Arg Term)
            argLam n f = (\ (Abs n (Arg i t)) -> Arg i $ Lam defaultArgInfo $ Abs n t) <$> bind "n" f
          let cas1 = applyN u $ map (<@> pure io) delta ++ as1

          let base | Nothing <- mtrX = cas1
                   | Just trX <- mtrX = do
                       let theTel = bind "j" $ \ j -> bind "i" $ \ i -> applyN xTel (map (<@> max i j) delta)
                       let theLeft = lamTel $ bind "i" $ \ i -> do
                             as01 <- mapM (open . unArg) =<< (absApp <$> as01 <*> i)
                             con_ixs `applyN` (map (<@> i) delta ++ as01)
                       theLeft <- mapM open =<< theLeft
                       theRight <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> do
                         con_ixs `applyN` (map (<@> pure io) delta ++ as1)

                       trx' <- transpPathPTel' theTel x theRight phi theLeft
                       let args = liftM2 (++) (map (setHiding Hidden) <$> deltaArg (pure io)) (forM trx' $ \ q' -> do
                                                                       q' <- open q'
                                                                       argLam "i" $ \ i -> q' `argApp` neg i)
                       (apply (Def trX []) <$> args) <@> phi <@> cas1


          if null boundary then base else do

          -- We have to correct the boundary for path constructors.

          -- bline : Abs I ([phi] → ty)
          let blineFace = applyN bsysFace $ map (<@> pure io) delta ++ as1
          let bline = do
                let theTel = bind "j" $ \ j -> bind "i" $ \ i -> applyN xTel (map (<@> max i j) delta)
                let theLeft = lamTel $ bind "i" $ \ i -> do
                      as01 <- mapM (open . unArg) =<< (absApp <$> as01 <*> i)
                      con_ixs `applyN` (map (<@> i) delta ++ as01)
                theLeft <- mapM open =<< theLeft
                theRight <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> do
                  con_ixs `applyN` (map (<@> pure io) delta ++ as1)
                let q2_f = bind "i" $ \ i -> map unArg <$> trFillPathPTel' theTel x theRight phi theLeft i

                lam "i" $ \ i -> do
                let v0 = do
                     as01 <- mapM (open . unArg) =<< (absApp <$> as01 <*> i)
                     applyN bsys $ map (<@> i) delta ++ as01
                let squeezedv0 = ilam "o" $ \ o -> do
                      let
                        delta_f :: [NamesT TCM Term]
                        delta_f = for delta $ \ p -> lam "j" $ \ j -> p <@> (j `max` i)
                      x_f <- (mapM open =<<) $ lamTel $ bind "j" $ \ j ->
                                 (absApp <$> q2_f <*> j) `appTel` i
                      trD `applyN` delta_f `applyN` x_f `applyN` [phi `max` i, v0 <..> o]

                caseMaybe mtrX squeezedv0 $ \ trX -> ilam "o" $ \ o -> do
                  q2 <- transpPathPTel' theTel x theRight phi theLeft
                  let args = liftM2 (++) (map (setHiding Hidden) <$> deltaArg (pure io))
                                         (forM q2 $ \ q' -> do
                                            q' <- open q'
                                            argLam "j" $ \ j -> q' `argApp` (neg j `min` i))

                  (apply (Def trX []) <$> args) <@> (neg i `max` phi) <@> (squeezedv0 <..> o)
          hcomp
             rhsTy
             [(blineFace,lam "i" $ \ i -> bline <@> (neg i))
             ,(phi      ,lam "i" $ \ _ -> ilam "o" $ \ _ -> orig)
             ]
             base

        let
          (ps,rhsTy,rhs) = unAbsN $ unAbsN $ unAbsN $ unAbsN $ res
        mkClause gamma ps rhsTy rhs
  where
    mkClause gamma ps rhsTy rhs = do
      let
        c = Clause
            { clauseTel         = gamma
            , clauseType        = Just . argN $ rhsTy
            , namedClausePats   = ps
            , clauseFullRange   = noRange
            , clauseLHSRange    = noRange
            , clauseCatchall    = False
            , clauseBody        = Just $ rhs
            , clauseRecursive   = Nothing
            -- it is indirectly recursive through transp, does it count?
            , clauseUnreachable = Just False
            , clauseEllipsis    = NoEllipsis
            , clauseWhereModule = Nothing
            }
      reportSDoc "tc.data.transp.con" 20 $
        "gamma:" <+> prettyTCM gamma
      reportSDoc "tc.data.transp.con" 20 $ addContext gamma $
        "ps   :" <+> prettyTCM (patternsToElims ps)
      reportSDoc "tc.data.transp.con" 20 $ addContext gamma $
        "type :" <+> prettyTCM rhsTy
      reportSDoc "tc.data.transp.con" 20 $ addContext gamma $
        "body :" <+> prettyTCM rhs

      reportSDoc "tc.data.transp.con" 30 $
        addContext gamma $ "c:" <+> pretty c
      return c


defineKanOperationForFields
  :: Command
  -> (Maybe Term)            -- ^ PathCons, Δ.Φ ⊢ u : R δ
  -> (Term -> QName -> Term) -- ^ how to apply a "projection" to a term
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM (Maybe ((QName, Telescope, Type, [Dom Type], [Term]), Substitution))
defineKanOperationForFields cmd pathCons project name params fsT fns rect =
   case cmd of
       DoTransp -> runMaybeT $ do
         fsT' <- traverse (traverse (MaybeT . toCType)) fsT
         lift $ defineTranspForFields pathCons project name params fsT' fns rect
       DoHComp -> runMaybeT $ do
         fsT' <- traverse (traverse (MaybeT . toLType)) fsT
         rect' <- MaybeT $ toLType rect
         lift $ defineHCompForFields project name params fsT' fns rect'


-- invariant: resulting tel Γ is such that Γ = ... , (φ : I), (a0 : ...)
--            where a0 has type matching the arguments of primTrans.
defineTranspForFields
  :: (Maybe Term)            -- ^ PathCons, Δ.Φ ⊢ u : R δ
  -> (Term -> QName -> Term) -- ^ how to apply a "projection" to a term
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Tele (Dom CType)   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM ((QName, Telescope, Type, [Dom Type], [Term]), Substitution)
     -- ^ @((name, tel, rtype, clause_types, bodies), sigma)@
     --   name: name of transport function for this constructor/record. clauses still missing.
     --   tel: Ξ telescope for the RHS, Ξ ⊃ (Δ^I, φ : I), also Ξ ⊢ us0 : Φ[δ 0]
     --   rtype: Ξ ⊢ T' := T[δ 1]
     --   clause_types: Ξ ⊢ Φ' := Φ[δ 1]
     --   bodies: Ξ ⊢ us1 : Φ'
     --   sigma:  Ξ, i : I ⊢ σ : Δ.Φ -- line [δ 0,us0] ≡ [δ 0,us1]
defineTranspForFields pathCons applyProj name params fsT fns rect = do
  interval <- primIntervalType
  let deltaI = expTelescope interval params
  iz <- primIZero
  io <- primIOne
  imin <- getPrimitiveTerm builtinIMin
  imax <- getPrimitiveTerm builtinIMax
  ineg <- getPrimitiveTerm builtinINeg
  transp <- getPrimitiveTerm builtinTrans
  -- por <- getPrimitiveTerm "primPOr"
  -- one <- primItIsOne
  reportSDoc "trans.rec" 20 $ pretty params
  reportSDoc "trans.rec" 20 $ pretty deltaI
  reportSDoc "trans.rec" 10 $ pretty fsT

  let thePrefix = "transp-"
  theName <- freshAbstractQName'_ $ thePrefix ++ P.prettyShow (A.qnameName name)

  reportSLn "trans.rec" 5 $ ("Generated name: " ++ show theName ++ " " ++ showQNameId theName)

  theType <- (abstract deltaI <$>) $ runNamesT [] $ do
              rect' <- open (runNames [] $ bind "i" $ \ x -> let _ = x `asTypeOf` pure (undefined :: Term) in
                                                             pure rect')
              nPi' "phi" primIntervalType $ \ phi ->
               (absApp <$> rect' <*> pure iz) --> (absApp <$> rect' <*> pure io)

  reportSDoc "trans.rec" 20 $ prettyTCM theType
  reportSDoc "trans.rec" 60 $ text $ "sort = " ++ show (getSort rect')

  lang <- getLanguage
  fun  <- emptyFunctionData
  noMutualBlock $ addConstant theName $
    (defaultDefn defaultArgInfo theName theType lang
       (FunctionDefn fun{ _funTerminates = Just True
                        , _funIsKanOp    = Just name
                        }))
      { defNoCompilation = True }
  -- ⊢ Γ = gamma = (δ : Δ^I) (φ : I) (u0 : R (δ i0))
  -- Γ ⊢     rtype = R (δ i1)
  TelV gamma rtype <- telView theType


  let
      -- (γ : Γ) ⊢ transpR γ : rtype
      theTerm = Def theName [] `apply` teleArgs gamma

      -- (γ : Γ) ⊢ (flatten Φ[δ i1])[n ↦ f_n (transpR γ)]
      clause_types = parallelS [theTerm `applyProj` (unArg fn)
                               | fn <- reverse fns] `applySubst`
                       flattenTel (singletonS 0 io `applySubst` fsT') -- Γ, Φ[δ i1] ⊢ flatten Φ[δ i1]

      -- Γ, i : I ⊢ [δ i] : Δ
      delta_i = (liftS 1 (raiseS (size gamma - size deltaI)) `composeS` sub params) -- Defined but not used

      -- Γ, i : I ⊢ Φ[δ i]
      fsT' = (liftS 1 (raiseS (size gamma - size deltaI)) `composeS` sub params)  `applySubst`
               fsT -- Δ ⊢ Φ
      lam_i = Lam defaultArgInfo . Abs "i"



      -- (δ , φ , u0) : Γ ⊢ φ : I
      -- the_phi = var 1
      -- -- (δ , φ , u0) : Γ ⊢ u0 : R (δ i0)
      -- the_u0  = var 0

      -- Γ' = (δ : Δ^I, φ : I)
      gamma' = telFromList $ take (size gamma - 1) $ telToList gamma

      -- δ : Δ^I, φ : F ⊢ [δ 0] : Δ
      d0 :: Substitution
      d0 = wkS 1 -- Δ^I, φ : F ⊢ Δ
                       (consS iz IdS `composeS` sub params) -- Δ^I ⊢ Δ
                                 -- Δ^I , i:I ⊢ sub params : Δ

      -- Ξ , Ξ ⊢ θ : Γ, Ξ ⊢ φ, Ξ ⊢ u : R (δ i0), Ξ ⊢ us : Φ[δ i0]
      (tel,theta,the_phi,the_u0, the_fields) =
        case pathCons of
          -- (δ : Δ).Φ ⊢ u : R δ
          Just u -> (abstract gamma' (d0 `applySubst` fmap (fmap fromCType) fsT) -- Ξ = δ : Δ^I, φ : F, _ : Φ[δ i0]
                    , (liftS (size fsT) d0 `applySubst` u) `consS` raiseS (size fsT)
                    , raise (size fsT) (var 0)
                    , (liftS (size fsT) d0 `applySubst` u)
                    , drop (size gamma') $ map unArg $ teleArgs tel)
          Nothing -> (gamma, IdS, var 1, var 0, map (\ fname -> var 0 `applyProj` unArg fname) fns )

      fsT_tel = (liftS 1 (raiseS (size tel - size deltaI)) `composeS` sub params) `applySubst` fsT

      iMin x y = imin `apply` [argN x, argN y]
      iMax x y = imax `apply` [argN x, argN y]
      iNeg x = ineg `apply` [argN x]

      -- .. ⊢ field : filled_ty' i0
      mkBody (field, filled_ty') = do
        let
          filled_ty = lam_i $ (unEl . fromCType . unDom) filled_ty'
          -- Γ ⊢ l : I -> Level of filled_ty
        -- sort <- reduce $ getSort $ unDom filled_ty'
        case unDom filled_ty' of
          LType (LEl l _) -> do
            let lvl = lam_i $ Level l
            return $ runNames [] $ do
             lvl <- open lvl
             phi <- open the_phi
             field <- open field
             pure transp <#> lvl <@> pure filled_ty
                                 <@> phi
                                 <@> field
          -- interval arg
          ClosedType{}  ->
            return $ runNames [] $ do
              field <- open field
              field
  let
        -- ' Ξ , i : I ⊢ τ = [(\ j → δ (i ∧ j)), φ ∨ ~ i, u] : Ξ
        tau = parallelS $ us ++ (phi `iMax` iNeg (var 0))
                        : map (\ d -> Lam defaultArgInfo $ Abs "i" $ raise 1 d `apply` [argN $ (iMin (var 0) (var 1))]) ds
         where
          -- Ξ, i : I
          (us, phi:ds) = splitAt (size tel - size gamma') $ reverse (raise 1 (map unArg (teleArgs tel)))

  let
    go acc [] = return []
    go acc ((fname,field_ty) : ps) = do
      -- Ξ, i : I, Φ[δ i]|_f ⊢ Φ_f = field_ty
      -- Ξ ⊢ b : field_ty [i := i1][acc]
      -- Ξ ⊢ parallesS acc : Φ[δ i1]|_f
      -- Ξ , i : I ⊢ τ = [(\ j → δ (i ∨ j), φ ∨ ~ i, us] : Ξ
      -- Ξ , i : I ⊢ parallesS (acc[τ]) : Φ[δ i1]|_f
      -- Ξ, i : I ⊢ field_ty [parallesS (acc[τ])]
      let
        filled_ty = parallelS (tau `applySubst` acc) `applySubst` field_ty
      b <- mkBody (fname,filled_ty)
      bs <- go (b : acc) ps
      return $ b : bs

  bodys <- go [] (zip the_fields (map (fmap snd) $ telToList fsT_tel)) -- ∀ f.  Ξ, i : I, Φ[δ i]|_f ⊢ Φ[δ i]_f
  let
    -- Ξ, i : I ⊢ ... : Δ.Φ
    theSubst = reverse (tau `applySubst` bodys) ++# (liftS 1 (raiseS (size tel - size deltaI)) `composeS` sub params)
  return $ ((theName, tel, theta `applySubst` rtype, map (fmap fromCType) clause_types, bodys), theSubst)
  where
    -- record type in 'exponentiated' context
    -- (params : Δ^I), i : I |- T[params i]
    rect' = sub params `applySubst` rect
    -- Δ^I, i : I |- sub Δ : Δ
    sub tel = expS $ size tel

-- invariant: resulting tel Γ is such that Γ = (δ : Δ), (φ : I), (u : ...), (a0 : R δ))
--            where u and a0 have types matching the arguments of primHComp.
defineHCompForFields
  :: (Term -> QName -> Term) -- ^ how to apply a "projection" to a term
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Tele (Dom LType)   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> LType        -- ^ record type (δ : Δ) ⊢ R[δ]
  -> TCM ((QName, Telescope, Type, [Dom Type], [Term]),Substitution)
defineHCompForFields applyProj name params fsT fns rect = do
  interval <- primIntervalType
  let delta = params
  iz <- primIZero
  io <- primIOne
  imin <- getPrimitiveTerm builtinIMin
  imax <- getPrimitiveTerm builtinIMax
  tIMax <- getPrimitiveTerm builtinIMax
  ineg <- getPrimitiveTerm builtinINeg
  hcomp <- getPrimitiveTerm builtinHComp
  transp <- getPrimitiveTerm builtinTrans
  por <- getPrimitiveTerm builtinPOr
  one <- primItIsOne
  reportSDoc "comp.rec" 20 $ text $ show params
  reportSDoc "comp.rec" 20 $ text $ show delta
  reportSDoc "comp.rec" 10 $ text $ show fsT

  let thePrefix = "hcomp-"
  theName <- freshAbstractQName'_ $ thePrefix ++ P.prettyShow (A.qnameName name)

  reportSLn "hcomp.rec" 5 $ ("Generated name: " ++ show theName ++ " " ++ showQNameId theName)

  theType <- (abstract delta <$>) $ runNamesT [] $ do
              rect <- open $ fromLType rect
              nPi' "phi" primIntervalType $ \ phi ->
               nPi' "i" primIntervalType (\ i ->
                pPi' "o" phi $ \ _ -> rect) -->
               rect --> rect

  reportSDoc "hcomp.rec" 20 $ prettyTCM theType
  reportSDoc "hcomp.rec" 60 $ text $ "sort = " ++ show (lTypeLevel rect)

  lang <- getLanguage
  fun  <- emptyFunctionData
  noMutualBlock $ addConstant theName $
    (defaultDefn defaultArgInfo theName theType lang
       (FunctionDefn fun{ _funTerminates = Just True
                        , _funIsKanOp    = Just name
                        }))
      { defNoCompilation = True }
  --   ⊢ Γ = gamma = (δ : Δ) (φ : I) (_ : (i : I) -> Partial φ (R δ)) (_ : R δ)
  -- Γ ⊢     rtype = R δ
  TelV gamma rtype <- telView theType

  let -- Γ ⊢ R δ
      drect_gamma = raiseS (size gamma - size delta) `applySubst` rect

  reportSDoc "hcomp.rec" 60 $ text $ "sort = " ++ show (lTypeLevel drect_gamma)

  let

      -- (γ : Γ) ⊢ hcompR γ : rtype
      compTerm = Def theName [] `apply` teleArgs gamma

      -- (δ, φ, u, u0) : Γ ⊢ φ : I
      the_phi = var 2
      -- (δ, φ, u, u0) : Γ ⊢ u : (i : I) → [φ] → R (δ i)
      the_u   = var 1
      -- (δ, φ, u, u0) : Γ ⊢ u0 : R (δ i0)
      the_u0  = var 0

      -- ' (δ, φ, u, u0) : Γ ⊢ fillR Γ : (i : I) → rtype[ δ ↦ (\ j → δ (i ∧ j))]
      fillTerm = runNames [] $ do
        rect   <- open . unEl  . fromLType  $ drect_gamma
        lvl    <- open . Level . lTypeLevel $ drect_gamma
        params <- mapM open $ take (size delta) $ teleArgs gamma
        phi    <- open the_phi
        w      <- open the_u
        w0     <- open the_u0
        -- (δ : Δ, φ : I, w : .., w0 : R δ) ⊢
        -- ' fillR Γ = λ i → hcompR δ (φ ∨ ~ i) (\ j → [ φ ↦ w (i ∧ j) , ~ i ↦ w0 ]) w0
        --           = hfillR δ φ w w0
        lam "i" $ \ i -> do
          args <- sequence params
          psi  <- pure imax <@> phi <@> (pure ineg <@> i)
          u <- lam "j" (\ j -> pure por <#> lvl
                                        <@> phi
                                        <@> (pure ineg <@> i)
                                        <#> lam "_" (\ o -> rect)
                                        <@> (w <@> (pure imin <@> i <@> j))
                                        <@> lam "_" (\ o -> w0) -- TODO wait for i = 0
                       )
          u0 <- w0
          pure $ Def theName [] `apply` (args ++ [argN psi, argN u, argN u0])

      -- (γ : Γ) ⊢ (flatten Φ)[n ↦ f_n (compR γ)]
      clause_types = parallelS [compTerm `applyProj` (unArg fn)
                               | fn <- reverse fns] `applySubst`
                       flattenTel (raiseS (size gamma - size delta) `applySubst` fsT) -- Γ, Φ ⊢ flatten Φ
      -- Δ ⊢ Φ = fsT
      -- Γ, i : I ⊢ Φ'
      fsT' = raiseS ((size gamma - size delta) + 1) `applySubst` fsT

      -- Γ, i : I ⊢ (flatten Φ')[n ↦ f_n (fillR Γ i)]
      filled_types = parallelS [raise 1 fillTerm `apply` [argN $ var 0] `applyProj` (unArg fn)
                               | fn <- reverse fns] `applySubst`
                       flattenTel fsT' -- Γ, i : I, Φ' ⊢ flatten Φ'


  comp <- do
        let
          imax i j = pure tIMax <@> i <@> j
        let forward la bA r u = pure transp <#> lam "i" (\ i -> la <@> (i `imax` r))
                                            <@> lam "i" (\ i -> bA <@> (i `imax` r))
                                            <@> r
                                            <@> u
        return $ \ la bA phi u u0 ->
          pure hcomp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                      <@> lam "i" (\ i -> ilam "o" $ \ o ->
                              forward la bA i (u <@> i <..> o))
                      <@> forward la bA (pure iz) u0
  let
      mkBody (fname, filled_ty') = do
        let
          proj t = (`applyProj` unArg fname) <$> t
          filled_ty = Lam defaultArgInfo (Abs "i" $ (unEl . fromLType . unDom) filled_ty')
          -- Γ ⊢ l : I -> Level of filled_ty
        l <- reduce $ lTypeLevel $ unDom filled_ty'
        let lvl = Lam defaultArgInfo (Abs "i" $ Level l)
        return $ runNames [] $ do
             lvl       <- open lvl
             phi       <- open the_phi
             w         <- open the_u
             w0        <- open the_u0
             filled_ty <- open filled_ty

             comp lvl
                  filled_ty
                  phi
                  (lam "i" $ \ i -> ilam "o" $ \ o -> proj $ w <@> i <..> o) -- TODO wait for phi = 1
                  (proj w0)

  reportSDoc "hcomp.rec" 60 $ text $ "filled_types sorts:" ++ show (map (getSort . fromLType . unDom) filled_types)

  bodys <- mapM mkBody (zip fns filled_types)
  return $ ((theName, gamma, rtype, map (fmap fromLType) clause_types, bodys),IdS)


getGeneralizedParameters :: Set Name -> QName -> TCM [Maybe Name]
getGeneralizedParameters gpars name | Set.null gpars = return []
getGeneralizedParameters gpars name = do
  -- Drop the named parameters that shouldn't be in scope (if the user
  -- wrote a split data type)
  let inscope x = x <$ guard (Set.member x gpars)
  map (>>= inscope) . defGeneralizedParams <$> (instantiateDef =<< getConstInfo name)

-- | Bind the named generalized parameters.
bindGeneralizedParameters :: [Maybe Name] -> Type -> (Telescope -> Type -> TCM a) -> TCM a
bindGeneralizedParameters [] t ret = ret EmptyTel t
bindGeneralizedParameters (name : names) t ret =
  case unEl t of
    Pi a b -> ext $ bindGeneralizedParameters names (unAbs b) $ \ tel t -> ret (ExtendTel a (tel <$ b)) t
      where
        ext | Just x <- name = addContext (x, a)
            | otherwise      = addContext (absName b, a)
    _      -> __IMPOSSIBLE__

-- | Bind the parameters of a datatype.
--
--   We allow omission of hidden parameters at the definition site.
--   Example:
--   @
--     data D {a} (A : Set a) : Set a
--     data D A where
--       c : A -> D A
--   @

bindParameters
  :: Int            -- ^ Number of parameters
  -> [A.LamBinding] -- ^ Bindings from definition site.
  -> Type           -- ^ Pi-type of bindings coming from signature site.
  -> (Telescope -> Type -> TCM a)
     -- ^ Continuation, accepting parameter telescope and rest of type.
     --   The parameters are part of the context when the continutation is invoked.
  -> TCM a

bindParameters 0 [] a ret = ret EmptyTel a

bindParameters 0 (par : _) _ _ = setCurrentRange par $
  typeError $ UnexpectedParameter par

bindParameters npars [] t ret =
  case unEl t of
    Pi a b | not (visible a) -> do
              x <- freshName_ (absName b)
              bindParameter npars [] x a b ret
           | otherwise ->
              typeError $ ExpectedBindingForParameter a b
    _ -> __IMPOSSIBLE__

bindParameters npars par@(A.DomainFull (A.TBind _ _ xs e) : bs) a ret =
  setCurrentRange par $
  typeError $ UnexpectedTypeSignatureForParameter xs

bindParameters _ (A.DomainFull A.TLet{} : _) _ _ = __IMPOSSIBLE__

bindParameters _ (par@(A.DomainFree _ arg) : ps) _ _
  | getModality arg /= defaultModality = setCurrentRange par $
      typeError $ UnexpectedModalityAnnotationInParameter par

bindParameters npars ps0@(par@(A.DomainFree _ arg) : ps) t ret = do
  let x          = namedArg arg
      TelV tel _ = telView' t
  case insertImplicit arg $ telToList tel of
    NoInsertNeeded -> continue ps $ A.unBind $ A.binderName x
    ImpInsert _    -> continue ps0 =<< freshName_ (absName b)
    BadImplicits   -> setCurrentRange par $
      typeError $ UnexpectedParameter par
    NoSuchName x   -> setCurrentRange par $
      typeError $ NoParameterOfName x
  where
    Pi dom@(Dom{domInfo = info', unDom = a}) b = unEl t -- TODO:: Defined but not used: info', a
    continue ps x = bindParameter npars ps x dom b ret

bindParameter :: Int -> [A.LamBinding] -> Name -> Dom Type -> Abs Type -> (Telescope -> Type -> TCM a) -> TCM a
bindParameter npars ps x a b ret =
  addContext (x, a) $
    bindParameters (npars - 1) ps (absBody b) $ \ tel s ->
      ret (ExtendTel a $ Abs (nameToArgName x) tel) s

-- | Check that the arguments to a constructor fits inside the sort of the datatype.
--   The third argument is the type of the constructor.
--
--   When @--without-K@ is active and the type is fibrant the
--   procedure also checks that the type is usable at the current
--   modality. See #4784 and #5434.
--
--   As a side effect, return the arity of the constructor.

fitsIn :: QName -> UniverseCheck -> [IsForced] -> Type -> Sort -> TCM Int
fitsIn con uc forceds conT s = do
  reportSDoc "tc.data.fits" 10 $
    sep [ "does" <+> prettyTCM conT
        , "of sort" <+> prettyTCM (getSort conT)
        , "fit in" <+> prettyTCM s <+> "?"
        ]
  -- The code below would be simpler, but doesn't allow datatypes
  -- to be indexed by the universe level.
  -- s' <- instantiateFull (getSort t)
  -- noConstraints $ s' `leqSort` s

  whenM withoutKOption $ do
    q <- viewTC eQuantity
    usableAtModality' (Just s) ConstructorType (setQuantity q unitModality) (unEl conT)

  li <- optLargeIndices <$> pragmaOptions
  fitsIn' li forceds conT s
  where
  fitsIn' li forceds t s = do
    vt <- do
      t <- pathViewAsPi t
      return $ case t of
                    Left (a,b)     -> Just (True ,a,b)
                    Right (El _ t) | Pi a b <- t
                                   -> Just (False,a,b)
                    _              -> Nothing
    case vt of
      Just (isPath, dom, b) -> do
        -- Lucas, 23-11-2022: we re-check the type of the constructor argument
        -- with the right polarity annotations in context.
        arg <- instantiateFull (unEl (unDom dom))
        reportSDoc "tc.polarity" 40 $
          sep [ "checking constructor domain"
              , prettyTCM (unEl $ unDom dom)
              , "("
              , prettyTCM (show arg)
              , ")"
              , "against sort"
              , prettyTCM (getSort dom)
              ]
        checkInternal arg CmpLeq (sort (getSort dom))
        let
          (forced, forceds') = nextIsForced forceds
          isf = isForced forced

        unless (isf && li) $ do
          sa <- reduce $ getSort dom
          unless (isPath || uc == NoUniverseCheck || sa == SizeUniv) $
            traceCall (CheckConArgFitsIn con isf (unDom dom) s) $
            fitSort sa s

        addContext (absName b, dom) $ do
          succ <$> fitsIn' li forceds' (absBody b) (raise 1 s)
      _ -> do
        fitSort (getSort t) s
        return 0
  -- catch hard error from sort comparison to turn it into a soft error
  fitSort sa s = leqSort sa s `catchError` \ err ->
    warning $ ConstructorDoesNotFitInData con sa s err

-- | When --without-K is enabled, we should check that the sorts of
--   the index types fit into the sort of the datatype.
checkIndexSorts :: Sort -> Telescope -> TCM ()
checkIndexSorts s = \case
  EmptyTel -> return ()
  ExtendTel a tel' -> do
    let sa = getSort a
    -- Andreas, 2020-10-19, allow Size indices
    unless (sa == SizeUniv) $ sa `leqSort` s
    underAbstraction a tel' $ checkIndexSorts (raise 1 s)

-- | Return the parameters that share variables with the indices
-- nonLinearParameters :: Int -> Type -> TCM [Int]
-- nonLinearParameters nPars t =

data IsPathCons = PathCons | PointCons
  deriving (Eq,Show)

-- | Check that a type constructs something of the given datatype. The first
--   argument is the number of parameters to the datatype and the second the
--   number of additional non-parameters in the context (1 when generalizing, 0
--   otherwise).
--
constructs :: Int -> Int -> Type -> QName -> TCM IsPathCons
constructs nofPars nofExtraVars t q = constrT nofExtraVars t
    where
        -- The number n counts the proper (non-parameter) constructor arguments.
        constrT :: Nat -> Type -> TCM IsPathCons
        constrT n t = do
            t <- reduce t
            pathV <- pathViewAsPi'whnf
            case unEl t of
                Pi _ (NoAbs _ b)  -> constrT n b
                Pi a b            -> underAbstraction a b $ constrT (n + 1)
                  -- OR: addCxtString (absName b) a $ constrT (n + 1) (absBody b)
                _ | Left ((a,b),_) <- pathV t -> do
                      _ <- case b of
                             NoAbs _ b -> constrT n b
                             b         -> underAbstraction a b $ constrT (n + 1)
                      return PathCons
                Def d es | d == q -> do
                  let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                  let (pars, ixs) = splitAt nofPars vs
                  -- check that the constructor parameters are the data parameters
                  checkParams n pars
                  return PointCons
                MetaV{} -> do
                  def <- getConstInfo q
                  -- Analyse the type of q (name of the data type)
                  let td = defType def
                  TelV tel core <- telView td
                  -- Construct the parameter arguments
                  -- The parameters are @n + nofPars - 1 .. n@
                  let us = zipWith (\ arg x -> var x <$ arg ) (telToArgs tel) $
                             take nofPars $ downFrom (nofPars + n)
                  -- The indices are fresh metas
                  xs <- newArgsMeta =<< piApplyM td us
                  let t' = El (raise n $ dataSort $ theDef def) $ Def q $ map Apply $ us ++ xs
                  -- Andreas, 2017-11-07, issue #2840
                  -- We should not postpone here, otherwise we might upset the positivity checker.
                  ifM (tryConversion $ equalType t t')
                      (constrT n t')
                      (typeError $ ShouldEndInApplicationOfTheDatatype t)
                _ -> typeError $ ShouldEndInApplicationOfTheDatatype t

        checkParams n vs = zipWithM_ sameVar vs ps
            where
                nvs = length vs
                ps  = reverse $ take nvs [n..]

                sameVar arg i
                  -- skip irrelevant parameters
                  | isIrrelevant arg = return ()
                  | otherwise = do
                    t <- typeOfBV i
                    equalTerm t (unArg arg) (var i)


-- | Is the type coinductive? Returns 'Nothing' if the answer cannot
-- be determined.

isCoinductive :: Type -> TCM (Maybe Bool)
isCoinductive t = do
  El s t <- reduce t
  case t of
    Def q _ -> do
      def <- getConstInfo q
      case theDef def of
        Axiom       {} -> return (Just False)
        DataOrRecSig{} -> return Nothing
        Function    {} -> return Nothing
        Datatype    {} -> return (Just False)
        Record      {  recInduction = Just CoInductive } -> return (Just True)
        Record      {  recInduction = _                } -> return (Just False)
        GeneralizableVar{} -> __IMPOSSIBLE__
        Constructor {} -> __IMPOSSIBLE__
        Primitive   {} -> __IMPOSSIBLE__
        PrimitiveSort{} -> __IMPOSSIBLE__
        AbstractDefn{} -> __IMPOSSIBLE__
    Var   {} -> return Nothing
    Lam   {} -> __IMPOSSIBLE__
    Lit   {} -> __IMPOSSIBLE__
    Level {} -> __IMPOSSIBLE__
    Con   {} -> __IMPOSSIBLE__
    Pi    {} -> return (Just False)
    Sort  {} -> return (Just False)
    MetaV {} -> return Nothing
    DontCare{} -> __IMPOSSIBLE__
    Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s
