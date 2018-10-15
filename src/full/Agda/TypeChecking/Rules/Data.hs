{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}

module Agda.TypeChecking.Rules.Data where

import Control.Monad

import Data.List (genericTake)
import Data.Maybe (fromMaybe)

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
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
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

import Agda.Interaction.Options

import Agda.Utils.Except
import Agda.Utils.List
import Agda.Utils.Monad
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Datatypes
---------------------------------------------------------------------------

-- | Type check a datatype definition. Assumes that the type has already been
--   checked.
checkDataDef :: Info.DefInfo -> QName -> UniverseCheck -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkDataDef i name uc ps cs =
    traceCall (CheckDataDef (getRange name) (qnameName name) ps cs) $ do -- TODO!! (qnameName)

        -- Add the datatype module
        addSection (qnameToMName name)

        -- Look up the type of the datatype.
        t <- instantiateFull =<< typeOfConst name

        -- Make sure the shape of the type is visible
        let unTelV (TelV tel a) = telePi tel a
        t <- unTelV <$> telView t

        -- Top level free vars
        freeVars <- getContextSize

        -- The parameters are in scope when checking the constructors.
        dataDef <- bindParameters ps t $ \tel t0 -> do

            -- Parameters are always hidden in constructors
            let tel' = hideAndRelParams <$> tel
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

            reportSDoc "tc.data.sort" 20 $ vcat
              [ "checking datatype" <+> prettyTCM name
              , nest 2 $ vcat
                [ "type (parameters instantiated):   " <+> prettyTCM t0
                , "type (full):   " <+> prettyTCM t
                , "sort:   " <+> prettyTCM s
                , "indices:" <+> text (show nofIxs)
                , "params:"  <+> text (show $ deepUnscope ps)
                ]
              ]
            let npars = size tel

            -- Change the datatype from an axiom to a datatype with no constructors.
            let dataDef = Datatype
                  { dataPars       = npars
                  , dataIxs        = nofIxs
                  , dataInduction  = Inductive
                  , dataClause     = Nothing
                  , dataCons       = []     -- Constructors are added later
                  , dataSort       = s
                  , dataAbstr      = Info.defAbstract i
                  , dataMutual     = Nothing
                  }

            escapeContext npars $ do
              addConstant name $
                defaultDefn defaultArgInfo name t dataDef
                -- polarity and argOcc.s determined by the positivity checker

            -- Check the types of the constructors
            mapM_ (checkConstructor name uc tel' nofIxs s) cs

            -- Return the data definition
            return dataDef

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
  -> TCM ()
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
        -- check that the type of the constructor is well-formed
        t <- workOnTypes $ isType_ e
        -- check that the type of the constructor ends in the data type
        n <- getContextSize
        debugEndsIn t d n
        constructs n t d
        -- compute which constructor arguments are forced
        forcedArgs <- computeForcingAnnotations t
        -- check that the sort (universe level) of the constructor type
        -- is contained in the sort of the data type
        -- (to avoid impredicative existential types)
        debugFitsIn s
        -- To allow propositional squash, we turn @Prop ℓ@ into @Set ℓ@
        -- for the purpose of checking the type of the constructors.
        let s' = case s of
              Prop l -> Type l
              _      -> s
        arity <- fitsIn uc forcedArgs t s'
        -- this may have instantiated some metas in s, so we reduce
        s <- reduce s
        debugAdd c t

        TelV fields _ <- telView t

        -- We assume that the current context matches the parameters
        -- of the datatype in an empty context (c.f. getContextSize above).
        params <- getContextTelescope

        -- add parameters to constructor type and put into signature
        let con = ConHead c Inductive [] -- data constructors have no projectable fields and are always inductive
        escapeContext (size tel) $ do

          cnames <- if nofIxs /= 0 || (Info.defAbstract i == AbstractDef) then return Nothing else do
            inTopContext $ do
              names <- forM [0 .. size fields - 1] (\ i -> freshAbstractQName'_ (P.prettyShow (A.qnameName c) ++ "-" ++ show i))

              -- nofIxs == 0 means the data type can be reconstructed
              -- by appling the QName d to the parameters.
              dataT <- El s <$> (pure $ Def d $ map Apply $ teleArgs params)

              reportSDoc "tc.data.con.comp" 5 $ vcat $
                [ "params =" <+> pretty params
                , "dataT  =" <+> pretty dataT
                , "fields =" <+> pretty fields
                , "names  =" <+> pretty names
                ]

              defineProjections d con params names fields dataT
              comp <- defineCompData d con params names fields dataT
              return $ fmap (\ x -> (x,names)) comp

          addConstant c $
            defaultDefn defaultArgInfo c (telePi tel t) $ Constructor
              { conPars   = size tel
              , conArity  = arity
              , conSrcCon = con
              , conData   = d
              , conAbstr  = Info.defAbstract i
              , conInd    = Inductive
              , conComp   = cnames
              , conForced = forcedArgs
              , conErased = []  -- computed during compilation to treeless
              }

          case cnames of
            Nothing -> return ()
            Just (_,names) -> mapM_ makeProjection names

        -- Add the constructor to the instance table, if needed
        when (Info.defInstance i == InstanceDef) $ do
          addNamedInstance c d

  where
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
               -> TCM (Maybe QName)
defineCompData d con params names fsT t = do
  haveCubicalThings <- do
    i  <- getBuiltin' builtinInterval
    iz <- getBuiltin' builtinIZero
    io <- getBuiltin' builtinIOne
    imin <- getPrimitiveTerm' "primIMin"
    imax <- getPrimitiveTerm' "primIMax"
    ineg <- getPrimitiveTerm' "primINeg"
    comp <- getPrimitiveTerm' "primComp"
    por <- getPrimitiveTerm' "primPOr"
    one <- getBuiltin' builtinItIsOne
    return $ maybe False (const True) $ sequence [i,iz,io,imin,imax,ineg,comp,por,one]
  sortsOk <- allM (t : map unDom (flattenTel fsT)) sortOk
  if not sortsOk || not haveCubicalThings then return Nothing else do
    (compName, gamma , ty, _ , bodies) <-
      defineCompForFields (\ t p -> apply (Def p []) [argN t]) d params fsT (map argN names) t
    let clause = Clause
            { clauseTel = gamma
            , clauseType = Just . argN $ ty
            , namedClausePats = teleNamedArgs gamma
            , clauseFullRange = noRange
            , clauseLHSRange  = noRange
            , clauseCatchall = False
            , clauseBody = Just $ Con con ConOSystem (map Apply $ map argN bodies) -- abstract gamma $ Body $ Con con (map argN bodies)
            , clauseUnreachable = Just False
            }
        cs = [clause]
    addClauses compName cs
    setCompiledClauses compName =<< inTopContext (compileClauses Nothing cs)
    setTerminates compName True
    return $ Just compName
  where
    sortOk :: Type -> TCM Bool
    sortOk a = reduce (getSort a) >>= \case
      Type{} -> return True
      _      -> return False

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
      reportSDoc "tc.data.proj" 20 $ sep [ "proj" <+> prettyTCM (i,ty) , nest 2 $ text . show $  projType ]

    let
      cpi  = ConPatternInfo Nothing False (Just $ argN $ raise (size fsT) t) False
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
          }

    noMutualBlock $ do
      let cs = [clause]
      cc <- inTopContext $ compileClauses Nothing cs
      let fun = emptyFunction
                { funClauses = cs
                , funTerminates = Just True
                , funCompiled = Just cc
                , funMutual = Just []
                }
      addConstant projName $
        (defaultDefn defaultArgInfo projName (unDom projType) fun)
          { defNoCompilation = True }
      inTopContext $ do
        reportSDoc "tc.data.proj.fun" 20 $ sep [ "proj" <+> prettyTCM i, nest 2 $ text . show $ fun ]


freshAbstractQName'_ :: String -> TCM QName
freshAbstractQName'_ s = freshAbstractQName noFixity' (C.Name noRange [C.Id $ s])

-- invariant: resulting tel Γ is such that Γ = ... , (φ : I), (u : ...) , (a0 : ...)
--            where u and a0 have types matching the arguments of primComp.
defineCompForFields
  :: (Term -> QName -> Term) -- ^ how to apply a "projection" to a term
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM (QName, Telescope, Type, [Dom Type], [Term])
defineCompForFields applyProj name params fsT fns rect = do
  interval <- elInf primInterval
  let deltaI = expTelescope interval params
  iz <- primIZero
  io <- primIOne
  imin <- getPrimitiveTerm "primIMin"
  imax <- getPrimitiveTerm "primIMax"
  ineg <- getPrimitiveTerm "primINeg"
  comp <- getPrimitiveTerm "primComp"
  por <- getPrimitiveTerm "primPOr"
  one <- primItIsOne
  reportSDoc "comp.rec" 20 $ text $ show params
  reportSDoc "comp.rec" 20 $ text $ show deltaI
  reportSDoc "comp.rec" 10 $ text $ show fsT
  compName <- freshAbstractQName'_ $ "comp-" ++ P.prettyShow (A.qnameName name)
  reportSLn "comp.rec" 5 $ ("Generated name: " ++ show compName ++ " " ++ showQNameId compName)
  compType <- (abstract deltaI <$>) $ runNamesT [] $ do
              rect' <- open (runNames [] $ bind "i" $ \ x -> let _ = x `asTypeOf` pure (undefined :: Term) in
                                                             pure rect')
              nPi' "phi" (elInf $ cl primInterval) $ \ phi ->
               (nPi' "i" (elInf $ cl primInterval) $ \ i ->
                pPi' "o" phi $ \ _ -> absApp <$> rect' <*> i) -->
               (absApp <$> rect' <*> pure iz) --> (absApp <$> rect' <*> pure io)
  reportSDoc "comp.rec" 20 $ prettyTCM compType
  reportSDoc "comp.rec" 60 $ text $ "sort = " ++ show (getSort rect')

  noMutualBlock $ addConstant compName $ (defaultDefn defaultArgInfo compName compType
    (emptyFunction { funTerminates = Just True }))
    { defNoCompilation = True }
  --   ⊢ Γ = gamma = (δ : Δ^I) (φ : I) (_ : (i : I) -> Partial φ (R (δ i))) (_ : R (δ i0))
  -- Γ ⊢     rtype = R (δ i1)
  TelV gamma rtype <- telView compType

  let
      drect_gamma = liftS 1 (raiseS (size gamma - size deltaI)) `applySubst` rect'

  reportSDoc "comp.rec" 60 $ text $ "sort = " ++ show (getSort drect_gamma)

  let
      -- Γ, i : I ⊢ Φ
      fsT' = liftS 1 (raiseS (size gamma - size deltaI)) `applySubst`
              (sub params `applySubst` fsT) -- Δ^I, i : I ⊢ Φ

      -- Γ ⊢ rect_gamma_lvl : I -> Level
      -- Γ ⊢ rect_gamma     : (i : I) -> Set (rect_gamma_lvl i)  -- record type
      (rect_gamma_lvl, rect_gamma) = (lam_i (Level l) , lam_i (unEl drect_gamma))
        where
          lam_i = Lam defaultArgInfo . Abs "i"
          Type l = getSort drect_gamma

      -- Γ ⊢ compR Γ : rtype
      compTerm = Def compName [] `apply` teleArgs gamma

      -- Γ ⊢ fillR Γ : ..
      fillTerm = runNames [] $ do
        params <- mapM open $ take (size deltaI) $ teleArgs gamma
        [phi,w,w0] <- mapM (open . var) [2,1,0]
        lvl  <- open rect_gamma_lvl
        rect <- open rect_gamma
        -- (δ : Δ^I, φ : I, w : .., w0 : R (δ i0)) ⊢
        -- ' fillR Γ = λ i → compR (\ j → δ (i ∧ j)) (φ ∨ ~ i) (\ j → [ φ ↦ w (i ∧ j) , ~ i ↦ w0 ]) w0
        lam "i" $ \ i -> do
          args <- mapM (underArg $ \ bA -> lam "j" $ \ j -> bA <@> (pure imin <@> i <@> j)) params
          psi  <- pure imax <@> phi <@> (pure ineg <@> i)
          u <- lam "j" (\ j -> pure por <#> (lvl <@> (pure imin <@> i <@> j))
                                        <@> phi
                                        <@> (pure ineg <@> i)
                                        <#> (lam "_" $ \ o -> rect <@> (pure imin <@> i <@> j))
                                        <@> (w <@> (pure imin <@> i <@> j))
                                        <@> (lam "_" $ \ o -> w0) -- TODO wait for i = 0
                       )
          u0 <- w0
          pure $ Def compName [] `apply` (args ++ [argN psi, argN u, argN u0])
        where
          underArg k m = Arg <$> (argInfo <$> m) <*> (k (unArg <$> m))

      -- Γ ⊢ Φ[n ↦ f_n (compR Γ)]
      clause_types = parallelS [compTerm `applyProj` (unArg fn)
                               | fn <- reverse fns] `applySubst`
                       flattenTel (singletonS 0 io `applySubst` fsT') -- Γ, Φ ⊢ Φ

      -- Γ, i : I ⊢ Φ[n ↦ f_n (fillR Γ i)]
      filled_types = parallelS [raise 1 fillTerm `apply` [argN $ var 0] `applyProj` (unArg fn)
                               | fn <- reverse fns] `applySubst`
                       flattenTel fsT' -- Γ, i : I, Φ ⊢ Φ

      mkBody (fname, filled_ty') = do
        let
          proj t = (`applyProj` unArg fname) <$> t
          filled_ty = Lam defaultArgInfo (Abs "i" $ (unEl . unDom) filled_ty')
          -- Γ ⊢ l : I -> Level of filled_ty
        Type l <- reduce $ getSort $ unDom filled_ty'
        let lvl = Lam defaultArgInfo (Abs "i" $ Level l)
        return $ runNames [] $ do
             lvl <- open lvl
             [phi,w,w0] <- mapM (open . var) [2,1,0]
             pure comp <#> lvl <@> pure filled_ty
                               <@> phi
                               <@> (lam "i" $ \ i -> lam "o" $ \ o -> proj $ w <@> i <@> o) -- TODO wait for phi = 1
                               <@> proj w0

  reportSDoc "comp.rec" 60 $ text $ "filled_types sorts:" ++ show (map (getSort . unDom) filled_types)

  bodys <- mapM mkBody (zip fns filled_types)
  return $ (compName, gamma, rtype, clause_types, bodys)
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


-- | Bind the parameters of a datatype.
--
--   We allow omission of hidden parameters at the definition site.
--   Example:
--   @
--     data D {a} (A : Set a) : Set a
--     data D A where
--       c : A -> D A
--   @

bindParameters :: [A.LamBinding] -> Type -> (Telescope -> Type -> TCM a) -> TCM a
bindParameters = bindParameters' []

-- | Auxiliary function for 'bindParameters'.
bindParameters'
  :: [Type]         -- ^ @n@ replicas of type if @LamBinding@s are @DomainFree@s
                    --   that came from a @DomainFull@ of @n@ binders.
                    --   Should be comsumed whenever a @DomainFree@s are consumed.
  -> [A.LamBinding] -- ^ Bindings from definition site.
  -> Type           -- ^ Pi-type of bindings coming from signature site.
  -> (Telescope -> Type -> TCM a)
     -- ^ Continuation, accepting parameter telescope and rest of type.
     --   The parameters are part of the context when the continutation is invoked.
  -> TCM a

bindParameters' _ [] a ret = ret EmptyTel a

bindParameters' ts (A.DomainFull (A.TypedBindings _ (Arg info (A.TBind _ xs e))) : bs) a ret = do
  unless (null ts) __IMPOSSIBLE__
  t <- workOnTypes $ isType_ e
  bindParameters' (t <$ xs) (map (mergeHiding . fmap (A.DomainFree info)) xs ++ bs) a ret

bindParameters' _ (A.DomainFull (A.TypedBindings _ (Arg _ A.TLet{})) : _) _ _ =  -- line break!
  __IMPOSSIBLE__

bindParameters' ts0 ps0@(A.DomainFree info x : ps) t ret = do
  case unEl t of
    -- Andreas, 2011-04-07 ignore relevance information in binding?!
    Pi arg@(Dom{domInfo = info', unDom = a}) b -> do
      if | info == info'                  -> do
            -- Andreas, 2016-12-30, issue #1886:
            -- If type for binding is present, check its correctness.
            ts <- caseList ts0 (return []) $ \ t0 ts -> do
              equalType t0 a
              return ts
            continue ts ps $ A.unBind x

         | visible info, notVisible info' ->
            continue ts0 ps0 =<< freshName_ (absName b)

         | otherwise                      -> __IMPOSSIBLE__
             -- Andreas, 2016-12-30 Concrete.Definition excludes this case
      where
      continue ts ps x = do
        addContext (x, arg) $
          bindParameters' (raise 1 ts) ps (absBody b) $ \ tel s ->
            ret (ExtendTel arg $ Abs (nameToArgName x) tel) s
    _ -> __IMPOSSIBLE__


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
  t <- reduce t
  case unEl t of
    Pi dom b -> do
      withoutK <- optWithoutK <$> pragmaOptions
      let (forced,forceds') = nextIsForced forceds
      unless (isForced forced && not withoutK) $ do
        sa <- reduce $ getSort dom
        unless (not uc || sa == SizeUniv) $ sa `leqSort` s
      addContext (absName b, dom) $ do
        succ <$> fitsIn uc forceds' (absBody b) (raise 1 s)
    _ -> do
      getSort t `leqSort` s
      return 0

-- | Return the parameters that share variables with the indices
-- nonLinearParameters :: Int -> Type -> TCM [Int]
-- nonLinearParameters nPars t =

-- | Check that a type constructs something of the given datatype. The first
--   argument is the number of parameters to the datatype.
--
constructs :: Int -> Type -> QName -> TCM ()
constructs nofPars t q = constrT 0 t
    where
        -- The number n counts the proper (non-parameter) constructor arguments.
        constrT :: Nat -> Type -> TCM ()
        constrT n t = do
            t <- reduce t
            case unEl t of
                Pi _ (NoAbs _ b)  -> constrT n b
                Pi a b            -> underAbstraction a b $ constrT (n + 1)
                  -- OR: addCxtString (absName b) a $ constrT (n + 1) (absBody b)
                Def d es | d == q -> do
                  let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                  (pars, ixs) <- normalise $ splitAt nofPars vs
                  -- check that the constructor parameters are the data parameters
                  checkParams n pars
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
                  let t' = El (dataSort $ theDef def) $ Def q $ map Apply $ us ++ xs
                  -- Andreas, 2017-11-07, issue #2840
                  -- We should not postpone here, otherwise we might upset the positivity checker.
                  noConstraints $ equalType t t'
                  constrT n t'
                _ -> typeError $ ShouldEndInApplicationOfTheDatatype t

        checkParams n vs = zipWithM_ sameVar vs ps
            where
                nvs = size vs
                ps = genericTake nvs $ downFrom (n + nvs)

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
        Function    {} -> return Nothing
        Datatype    { dataInduction = CoInductive } -> return (Just True)
        Datatype    { dataInduction = Inductive   } -> return (Just False)
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
    Dummy s    -> __IMPOSSIBLE_VERBOSE__ s
