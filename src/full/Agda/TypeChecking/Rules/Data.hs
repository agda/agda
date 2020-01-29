{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Data where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import Data.Foldable (traverse_)
import Data.Maybe (fromMaybe, catMaybes, isJust)
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Views (deepUnscope)
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Fixity

import {-# SOURCE #-} Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin -- (primLevel)
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Generalize
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Forcing
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.ProjectionLike

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term ( isType_ )

import Agda.Utils.Except
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import qualified Agda.Utils.Pretty as P
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

        -- Make sure the shape of the type is visible
        let unTelV (TelV tel a) = telePi tel a
        t <- unTelV <$> telView t

        parNames <- getGeneralizedParameters gpars name

        -- Top level free vars
        freeVars <- getContextSize

        -- The parameters are in scope when checking the constructors.
        dataDef <- bindGeneralizedParameters parNames t $ \ gtel t0 ->
                   bindParameters (npars - length parNames) ps t0 $ \ ptel t0 -> do

            -- Parameters are always hidden in constructors
            let tel  = abstract gtel ptel
                tel' = hideAndRelParams <$> tel
            -- let tel' = hideTel tel

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
                  if any (`freeIn` s0) [0..nofIxs - 1] then typeError . GenericDocError =<<
                     fsep [ "The sort of" <+> prettyTCM name
                          , "cannot depend on its indices in the type"
                          , prettyTCM t0
                          ]
                  else throwError err
              reduce s

            -- when `--without-K`, all the indices should fit in the
            -- sort of the datatype (see #3420).
            let s' = case s of
                  Prop l -> Type l
                  _      -> s
            -- Andreas, 2019-07-16, issue #3916:
            -- NoUniverseCheck should also disable the index sort check!
            unless (uc == NoUniverseCheck) $
              whenM withoutKOption $ checkIndexSorts s' ixTel

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
            let dataDef = Datatype
                  { dataPars       = npars
                  , dataIxs        = nofIxs
                  , dataClause     = Nothing
                  , dataCons       = []     -- Constructors are added later
                  , dataSort       = s
                  , dataAbstr      = Info.defAbstract i
                  , dataMutual     = Nothing
                  , dataPathCons   = []     -- Path constructors are added later
                  }

            escapeContext __IMPOSSIBLE__ npars $ do
              addConstant name $
                defaultDefn defaultArgInfo name t dataDef
                -- polarity and argOcc.s determined by the positivity checker

            -- Check the types of the constructors
            pathCons <- forM cs $ \ c -> do
              isPathCons <- checkConstructor name uc tel' nofIxs s c
              return $ if isPathCons == PathCons then Just (A.axiomName c) else Nothing

            -- Return the data definition
            return dataDef{ dataPathCons = catMaybes pathCons }

        let s      = dataSort dataDef
            cons   = map A.axiomName cs  -- get constructor names

        -- Add the datatype to the signature with its constructors.
        -- It was previously added without them.
        addConstant name $
          defaultDefn defaultArgInfo name t $
            dataDef{ dataCons = cons }


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
        -- check that we are relevant
        case getRelevance ai of
          Relevant   -> return ()
          Irrelevant -> typeError $ GenericError $ "Irrelevant constructors are not supported"
          NonStrict  -> typeError $ GenericError $ "Shape-irrelevant constructors are not supported"
        case getQuantity ai of
          Quantityω{} -> return ()
          Quantity0{} -> typeError $ GenericError $ "Erased constructors are not supported"
          Quantity1{} -> typeError $ GenericError $ "Quantity-restricted constructors are not supported"
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
        arity <- traceCall (CheckConstructorFitsIn c t s') $ fitsIn uc forcedArgs t s'
        -- this may have instantiated some metas in s, so we reduce
        s <- reduce s
        debugAdd c t

        (TelV fields _, boundary) <- telViewUpToPathBoundaryP (-1) t

        -- We assume that the current context matches the parameters
        -- of the datatype in an empty context (c.f. getContextSize above).
        params <- getContextTelescope

        -- add parameters to constructor type and put into signature
        escapeContext __IMPOSSIBLE__ (size tel) $ do

          -- Cannot compose indexed inductive types yet.
          (con, comp, projNames) <- if nofIxs /= 0 || (Info.defAbstract i == AbstractDef)
            then return (ConHead c Inductive [], emptyCompKit, Nothing)
            else inTopContext $ do
              -- Name for projection of ith field of constructor c is just c-i
              names <- forM [0 .. size fields - 1] $ \ i ->
                freshAbstractQName'_ $ P.prettyShow (A.qnameName c) ++ "-" ++ show i

              -- nofIxs == 0 means the data type can be reconstructed
              -- by appling the QName d to the parameters.
              dataT <- El s <$> (pure $ Def d $ map Apply $ teleArgs params)

              reportSDoc "tc.data.con.comp" 5 $ vcat $
                [ "params =" <+> pretty params
                , "dataT  =" <+> pretty dataT
                , "fields =" <+> pretty fields
                , "names  =" <+> pretty names
                ]

              let con = ConHead c Inductive $ zipWith (<$) names $ map argFromDom $ telToList fields

              defineProjections d con params names fields dataT
              comp <- defineCompData d con params names fields dataT boundary
              return (con, comp, Just names)

          addConstant c $
            defaultDefn defaultArgInfo c (telePi tel t) $ Constructor
              { conPars   = size tel
              , conArity  = arity
              , conSrcCon = con
              , conData   = d
              , conAbstr  = Info.defAbstract i
              , conInd    = Inductive
              , conComp   = comp
              , conProj   = projNames
              , conForced = forcedArgs
              , conErased = Nothing  -- computed during compilation to treeless
              }

          -- Check generated projections for projection-likeness
          traverse_ (mapM_ makeProjection) $ projNames

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
          (_, t, isPathCons) <- generalizeType' s (check 1 e)
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
    [ builtinInterval
    , builtinIZero
    , builtinIOne
    , builtinIMin
    , builtinIMax
    , builtinINeg
    , builtinPOr
    , builtinItIsOne
    ]
  if not (all isJust required) then return $ emptyCompKit else do
    hcomp  <- whenDefined (null boundary) [builtinHComp,builtinTrans] (defineTranspOrHCompD DoHComp  d con params names fsT t boundary)
    transp <- whenDefined True            [builtinTrans]              (defineTranspOrHCompD DoTransp d con params names fsT t boundary)
    return $ CompKit
      { nameOfTransp = transp
      , nameOfHComp  = hcomp
      }
  where
    -- Δ^I, i : I |- sub Δ : Δ
    sub tel = parallelS [ var n `apply` [Arg defaultArgInfo $ var 0] | n <- [1..size tel] ]
    withArgInfo tel = zipWith Arg (map domInfo . telToList $ tel)
    defineTranspOrHCompD cmd d con params names fsT t boundary
      = do
      let project = (\ t p -> apply (Def p []) [argN t])
      stuff <- defineTranspOrHCompForFields cmd
                 (guard (not $ null boundary) >> (Just $ Con con ConOSystem $ teleElims fsT boundary))
                 project d params fsT (map argN names) t
      caseMaybe stuff (return Nothing) $ \ ((theName, gamma , ty, _cl_types , bodies), theSub) -> do

      iz <- primIZero
      body <- do
        case cmd of
          DoHComp -> return $ Con con ConOSystem (map Apply $ withArgInfo fsT bodies)
          DoTransp | null boundary -> return $ Con con ConOSystem (map Apply $ withArgInfo fsT bodies)
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
                                           <#> (ilam "o" $ \ _ -> unEl <$> la) <@> u0 <@> u1
              absAp x y = liftM2 absApp x y

              mkFace (r,(u1,u2)) = runNamesT [] $ do
                -- Γ
                phi <- open the_phi  -- (δ , φ , us) ⊢ φ
                -- Γ ⊢ ty = Abs i. R (δ i)
                ty <- open (Abs "i" $ (liftS 1 (raiseS (size gamma - size params)) `composeS` sub params) `applySubst` t)

                bind "i" $ \ i -> do
                  -- Γ, i
                  [r,u1,u2] <- mapM (open . applySubst theSub) [r,u1,u2]
                  psi <- imax r (ineg r)
                  let
                    -- Γ, i ⊢ squeeze u = primTrans (\ j -> ty [i := i ∨ j]) (φ ∨ i) u
                    squeeze u = cl primTrans
                                          <#> (lam "j" $ \ j -> lvlOfType <$> ty `absAp` (imax i j))
                                          <@> (lam "j" $ \ j -> unEl <$> ty `absAp` (imax i j))
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
        clause | null boundary
           = Clause
            { clauseTel = gamma
            , clauseType = Just . argN $ ty
            , namedClausePats = teleNamedArgs gamma
            , clauseFullRange = noRange
            , clauseLHSRange  = noRange
            , clauseCatchall = False
            , clauseBody = Just $ body
            , clauseUnreachable = Just False
            , clauseEllipsis = NoEllipsis
            }

               | otherwise
           = Clause
            { clauseTel = gamma
            , clauseType = Just . argN $ ty
            , namedClausePats = take (size gamma - size fsT) (teleNamedArgs gamma) ++ [argN $ unnamed $ up]
            , clauseFullRange = noRange
            , clauseLHSRange  = noRange
            , clauseCatchall = False
            , clauseBody = Just $ body
            , clauseUnreachable = Just False
            , clauseEllipsis = NoEllipsis
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
defineProjections :: QName      -- datatype name
                  -> ConHead
                  -> Telescope  -- Γ parameters
                  -> [QName]    -- projection names
                  -> Telescope  -- Γ ⊢ Φ field types
                  -> Type       -- Γ ⊢ T target type
                  -> TCM ()
defineProjections dataname con params names fsT t = do
  let
    -- Γ , (d : T) ⊢ Φ[n ↦ proj n d]
    fieldTypes = ([ Def f [] `apply` [argN $ var 0] | f <- reverse names ] ++# raiseS 1) `applySubst`
                    flattenTel fsT  -- Γ , Φ ⊢ Φ
    -- ⊢ Γ , (d : T)
    projTel = abstract params (ExtendTel (defaultDom t) (Abs "d" EmptyTel))
  forM_ (zip3 (downFrom (size fieldTypes)) names fieldTypes) $ \ (i,projName,ty) -> do
    let
      projType = abstract projTel <$> ty

    inTopContext $ do
      reportSDoc "tc.data.proj" 20 $ sep [ "proj" <+> prettyTCM (i,ty) , nest 2 $ prettyTCM projType ]

    let
      cpi  = ConPatternInfo defaultPatternInfo False False (Just $ argN $ raise (size fsT) t) False
      conp = defaultArg $ ConP con cpi $ teleNamedArgs fsT
      clause = Clause
          { clauseTel = abstract params fsT
          , clauseType = Just . argN $ ([Con con ConOSystem (map Apply $ teleArgs fsT)] ++# raiseS (size fsT)) `applySubst` unDom ty
          , namedClausePats = raise (size fsT) (teleNamedArgs params) ++ [Named Nothing <$> conp]
          , clauseFullRange = noRange
          , clauseLHSRange  = noRange
          , clauseCatchall = False
          , clauseBody = Just $ var i
          , clauseUnreachable = Just False
          , clauseEllipsis = NoEllipsis
          }

    noMutualBlock $ do
      let cs = [clause]
      (mst, _, cc) <- inTopContext $ compileClauses Nothing cs
      let fun = emptyFunction
                { funClauses = cs
                , funTerminates = Just True
                , funCompiled = Just cc
                , funSplitTree = mst
                , funMutual = Just []
                }
      addConstant projName $
        (defaultDefn defaultArgInfo projName (unDom projType) fun)
          { defNoCompilation = True }
      inTopContext $ do
        reportSDoc "tc.data.proj.fun" 60 $ sep [ "proj" <+> prettyTCM i, nest 2 $ pretty fun ]


freshAbstractQName'_ :: String -> TCM QName
freshAbstractQName'_ s = freshAbstractQName noFixity' (C.Name noRange C.InScope [C.Id $ s])


-- * Special cases of Type
-----------------------------------------------------------

-- | A @Type@ with sort @Type l@
--   Such a type supports both hcomp and transp.
data LType = LEl Level Term deriving (Eq,Show)

fromLType :: LType -> Type
fromLType (LEl l t) = El (Type l) t

lTypeLevel :: LType -> Level
lTypeLevel (LEl l t) = l

toLType :: MonadReduce m => Type -> m (Maybe LType)
toLType ty = do
  sort <- reduce $ getSort ty
  case sort of
    Type l -> return $ Just $ LEl l (unEl ty)
    _      -> return $ Nothing

instance Subst Term LType where
  applySubst rho (LEl l t) = LEl (applySubst rho l) (applySubst rho t)

-- | A @Type@ that either has sort @Type l@ or is a closed definition.
--   Such a type supports some version of transp.
--   In particular we want to allow the Interval as a @ClosedType@.
data CType = ClosedType QName | LType LType deriving (Eq,Show)

fromCType :: CType -> Type
fromCType (ClosedType q) = El Inf (Def q [])
fromCType (LType t) = fromLType t

toCType :: MonadReduce m => Type -> m (Maybe CType)
toCType ty = do
  sort <- reduce $ getSort ty
  case sort of
    Type l -> return $ Just $ LType (LEl l (unEl ty))
    Inf    -> do
      t <- reduce (unEl ty)
      case t of
        Def q [] -> return $ Just $ ClosedType q
        _        -> return $ Nothing
    _      -> return $ Nothing

instance Subst Term CType where
  applySubst rho t@ClosedType{} = t
  applySubst rho (LType t) = LType $ applySubst rho t


defineTranspOrHCompForFields
  :: TranspOrHComp
  -> (Maybe Term)            -- ^ PathCons, Δ.Φ ⊢ u : R δ
  -> (Term -> QName -> Term) -- ^ how to apply a "projection" to a term
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM (Maybe ((QName, Telescope, Type, [Dom Type], [Term]), Substitution))
defineTranspOrHCompForFields cmd pathCons project name params fsT fns rect =
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
defineTranspForFields pathCons applyProj name params fsT fns rect = do
  interval <- elInf primInterval
  let deltaI = expTelescope interval params
  iz <- primIZero
  io <- primIOne
  imin <- getPrimitiveTerm "primIMin"
  imax <- getPrimitiveTerm "primIMax"
  ineg <- getPrimitiveTerm "primINeg"
  transp <- getPrimitiveTerm builtinTrans
  por <- getPrimitiveTerm "primPOr"
  one <- primItIsOne
  reportSDoc "trans.rec" 20 $ text $ show params
  reportSDoc "trans.rec" 20 $ text $ show deltaI
  reportSDoc "trans.rec" 10 $ text $ show fsT

  let thePrefix = "transp-"
  theName <- freshAbstractQName'_ $ thePrefix ++ P.prettyShow (A.qnameName name)

  reportSLn "trans.rec" 5 $ ("Generated name: " ++ show theName ++ " " ++ showQNameId theName)

  theType <- (abstract deltaI <$>) $ runNamesT [] $ do
              rect' <- open (runNames [] $ bind "i" $ \ x -> let _ = x `asTypeOf` pure (undefined :: Term) in
                                                             pure rect')
              nPi' "phi" (elInf $ cl primInterval) $ \ phi ->
               (absApp <$> rect' <*> pure iz) --> (absApp <$> rect' <*> pure io)

  reportSDoc "trans.rec" 20 $ prettyTCM theType
  reportSDoc "trans.rec" 60 $ text $ "sort = " ++ show (getSort rect')

  noMutualBlock $ addConstant theName $ (defaultDefn defaultArgInfo theName theType
    (emptyFunction { funTerminates = Just True }))
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
      delta_i = (liftS 1 (raiseS (size gamma - size deltaI)) `composeS` sub params)

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
             [phi,field] <- mapM open [the_phi,field]
             pure transp <#> lvl <@> pure filled_ty
                                 <@> phi
                                 <@> field
          -- interval arg
          ClosedType{}  ->
            return $ runNames [] $ do
            [field] <- mapM open [field]
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
    sub tel = parallelS [ var n `apply` [Arg defaultArgInfo $ var 0] | n <- [1..size tel] ]
    -- given I type, and Δ telescope, build Δ^I such that
    -- (x : A, y : B x, ...)^I = (x : I → A, y : (i : I) → B (x i), ...)
    expTelescope :: Type -> Telescope -> Telescope
    expTelescope int tel = unflattenTel names ys
      where
        xs = flattenTel tel
        names = teleNames tel
        t = ExtendTel (defaultDom $ raise (size tel) int) (Abs "i" EmptyTel)
        s = sub tel
        ys = map (fmap (abstract t) . applySubst s) xs

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
  interval <- elInf primInterval
  let delta = params
  iz <- primIZero
  io <- primIOne
  imin <- getPrimitiveTerm "primIMin"
  imax <- getPrimitiveTerm "primIMax"
  tIMax <- getPrimitiveTerm "primIMax"
  ineg <- getPrimitiveTerm "primINeg"
  hcomp <- getPrimitiveTerm builtinHComp
  transp <- getPrimitiveTerm builtinTrans
  por <- getPrimitiveTerm "primPOr"
  one <- primItIsOne
  reportSDoc "comp.rec" 20 $ text $ show params
  reportSDoc "comp.rec" 20 $ text $ show delta
  reportSDoc "comp.rec" 10 $ text $ show fsT

  let thePrefix = "hcomp-"
  theName <- freshAbstractQName'_ $ thePrefix ++ P.prettyShow (A.qnameName name)

  reportSLn "hcomp.rec" 5 $ ("Generated name: " ++ show theName ++ " " ++ showQNameId theName)

  theType <- (abstract delta <$>) $ runNamesT [] $ do
              rect <- open $ fromLType rect
              nPi' "phi" (elInf $ cl primInterval) $ \ phi ->
               (nPi' "i" (elInf $ cl primInterval) $ \ i ->
                pPi' "o" phi $ \ _ -> rect) -->
               rect --> rect

  reportSDoc "hcomp.rec" 20 $ prettyTCM theType
  reportSDoc "hcomp.rec" 60 $ text $ "sort = " ++ show (lTypeLevel rect)

  noMutualBlock $ addConstant theName $ (defaultDefn defaultArgInfo theName theType
    (emptyFunction { funTerminates = Just True }))
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
        rect <- open . unEl  . fromLType  $ drect_gamma
        lvl  <- open . Level . lTypeLevel $ drect_gamma
        params     <- mapM open $ take (size delta) $ teleArgs gamma
        [phi,w,w0] <- mapM open [the_phi,the_u,the_u0]
        -- (δ : Δ, φ : I, w : .., w0 : R δ) ⊢
        -- ' fillR Γ = λ i → hcompR δ (φ ∨ ~ i) (\ j → [ φ ↦ w (i ∧ j) , ~ i ↦ w0 ]) w0
        --           = hfillR δ φ w w0
        lam "i" $ \ i -> do
          args <- sequence params
          psi  <- pure imax <@> phi <@> (pure ineg <@> i)
          u <- lam "j" (\ j -> pure por <#> lvl
                                        <@> phi
                                        <@> (pure ineg <@> i)
                                        <#> (lam "_" $ \ o -> rect)
                                        <@> (w <@> (pure imin <@> i <@> j))
                                        <@> (lam "_" $ \ o -> w0) -- TODO wait for i = 0
                       )
          u0 <- w0
          pure $ Def theName [] `apply` (args ++ [argN psi, argN u, argN u0])
        where
          underArg k m = Arg <$> (argInfo <$> m) <*> (k (unArg <$> m))

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
        let forward la bA r u = pure transp <#> (lam "i" $ \ i -> la <@> (i `imax` r))
                                            <@> (lam "i" $ \ i -> bA <@> (i `imax` r))
                                            <@> r
                                            <@> u
        return $ \ la bA phi u u0 ->
          pure hcomp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                      <@> (lam "i" $ \ i -> ilam "o" $ \ o ->
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
             lvl <- open lvl
             [phi,w,w0] <- mapM open [the_phi,the_u,the_u0]
             filled_ty <- open filled_ty

             comp lvl
                  filled_ty
                  phi
                  (lam "i" $ \ i -> lam "o" $ \ o -> proj $ w <@> i <@> o) -- TODO wait for phi = 1
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
  typeError . GenericDocError =<< do
    text "Unexpected parameter" <+> prettyA par

bindParameters npars [] t ret =
  case unEl t of
    Pi a b | not (visible a) -> do
              x <- freshName_ (absName b)
              bindParameter npars [] x a b ret
           | otherwise ->
              typeError . GenericDocError =<<
                sep [ "Expected binding for parameter"
                    , text (absName b) <+> text ":" <+> prettyTCM (unDom a) ]
    _ -> __IMPOSSIBLE__

bindParameters npars par@(A.DomainFull (A.TBind _ _ xs e) : bs) a ret =
  setCurrentRange par $
  typeError . GenericDocError =<< do
    let s | length xs > 1 = "s"
          | otherwise     = ""
    text ("Unexpected type signature for parameter" ++ s) <+> sep (map prettyA xs)

bindParameters _ (A.DomainFull A.TLet{} : _) _ _ = __IMPOSSIBLE__

bindParameters _ (par@(A.DomainFree _ arg) : ps) _ _
  | getModality arg /= defaultModality = setCurrentRange par $
     typeError . GenericDocError =<< do
       text "Unexpected modality/relevance annotation in" <+> prettyA par

bindParameters npars ps0@(par@(A.DomainFree _ arg) : ps) t ret = do
  let x          = namedArg arg
      TelV tel _ = telView' t
  case insertImplicit arg $ telToList tel of
    NoInsertNeeded -> continue ps $ A.unBind $ A.binderName x
    ImpInsert _    -> continue ps0 =<< freshName_ (absName b)
    BadImplicits   -> setCurrentRange par $
     typeError . GenericDocError =<< do
       text "Unexpected parameter" <+> prettyA par
    NoSuchName x   -> setCurrentRange par $
      typeError . GenericDocError =<< do
        text ("No parameter of name " ++ x)
  where
    Pi dom@(Dom{domInfo = info', unDom = a}) b = unEl t
    continue ps x = bindParameter npars ps x dom b ret

bindParameter :: Int -> [A.LamBinding] -> Name -> Dom Type -> Abs Type -> (Telescope -> Type -> TCM a) -> TCM a
bindParameter npars ps x a b ret =
  addContext (x, a) $
    bindParameters (npars - 1) ps (absBody b) $ \ tel s ->
      ret (ExtendTel a $ Abs (nameToArgName x) tel) s

-- | Check that the arguments to a constructor fits inside the sort of the datatype.
--   The third argument is the type of the constructor.
--
--   As a side effect, return the arity of the constructor.

fitsIn :: UniverseCheck -> [IsForced] -> Type -> Sort -> TCM Int
fitsIn uc forceds t s = do
  reportSDoc "tc.data.fits" 10 $
    sep [ "does" <+> prettyTCM t
        , "of sort" <+> prettyTCM (getSort t)
        , "fit in" <+> prettyTCM s <+> "?"
        ]
  -- The code below would be simpler, but doesn't allow datatypes
  -- to be indexed by the universe level.
  -- s' <- instantiateFull (getSort t)
  -- noConstraints $ s' `leqSort` s


  vt <- do
    t <- pathViewAsPi t
    return $ case t of
                  Left (a,b)     -> Just (True ,a,b)
                  Right (El _ t) | Pi a b <- t
                                 -> Just (False,a,b)
                  _              -> Nothing
  case vt of
    Just (isPath, dom, b) -> do
      withoutK <- withoutKOption
      let (forced,forceds') = nextIsForced forceds
      unless (isForced forced && not withoutK) $ do
        sa <- reduce $ getSort dom
        unless (isPath || uc == NoUniverseCheck || sa == SizeUniv) $ sa `leqSort` s
      addContext (absName b, dom) $ do
        succ <$> fitsIn uc forceds' (absBody b) (raise 1 s)
    _ -> do
      getSort t `leqSort` s
      return 0

-- | When --without-K is enabled, we should check that the sorts of
--   the index types fit into the sort of the datatype.
checkIndexSorts :: Sort -> Telescope -> TCM ()
checkIndexSorts s = \case
  EmptyTel -> return ()
  ExtendTel a tel' -> do
    getSort a `leqSort` s
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
                  (pars, ixs) <- normalise $ splitAt nofPars vs
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


{- UNUSED, Andreas 2012-09-13
-- | Force a type to be a specific datatype.
forceData :: QName -> Type -> TCM Type
forceData d (El s0 t) = liftTCM $ do
    t' <- reduce t
    d  <- canonicalName d
    case t' of
        Def d' _
            | d == d'   -> return $ El s0 t'
            | otherwise -> fail $ "wrong datatype " ++ show d ++ " != " ++ show d'
        MetaV m vs          -> do
            Defn {defType = t, theDef = Datatype{dataSort = s}} <- getConstInfo d
            ps <- newArgsMeta t
            noConstraints $ leqType (El s0 t') (El s (Def d ps)) -- TODO: need equalType?
            reduce $ El s0 t'
        _ -> typeError $ ShouldBeApplicationOf (El s0 t) d
-}

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
