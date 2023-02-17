{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation   #-}

module Agda.TypeChecking.Rules.Record where

import Prelude hiding (null, not, (&&), (||))

import Control.Monad
import Data.Maybe
import qualified Data.Set as Set

import Agda.Interaction.Options

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.CompiledClause (hasProjectionPatterns)
import Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.InstanceArguments

import Agda.TypeChecking.Rules.Data
  ( getGeneralizedParameters, bindGeneralizedParameters, bindParameters
  , checkDataSort, fitsIn, forceSort
  , defineCompData, defineKanOperationForFields
  )
import Agda.TypeChecking.Rules.Term ( isType_ )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkDecl)

import Agda.Utils.Boolean
import Agda.Utils.Function ( applyWhen )
import Agda.Utils.List (headWithDefault)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.POMonoid
import Agda.Syntax.Common.Pretty (render)
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

-- | @checkRecDef i name con ps contel fields@
--
--     [@name@]    Record type identifier.
--
--     [@con@]     Maybe constructor name and info.
--
--     [@ps@]      Record parameters.
--
--     [@contel@]  Approximate type of constructor (@fields@ -> dummy).
--                 Does not include record parameters.
--
--     [@fields@]  List of field signatures.
--
checkRecDef
  :: A.DefInfo                 -- ^ Position and other info.
  -> QName                     -- ^ Record type identifier.
  -> UniverseCheck             -- ^ Check universes?
  -> A.RecordDirectives        -- ^ (Co)Inductive, (No)Eta, (Co)Pattern, Constructor?
  -> A.DataDefParams           -- ^ Record parameters.
  -> A.Expr                    -- ^ Approximate type of constructor (@fields@ -> dummy).
                               --   Does not include record parameters.
  -> [A.Field]                 -- ^ Field signatures.
  -> TCM ()
checkRecDef i name uc (RecordDirectives ind eta0 pat con) (A.DataDefParams gpars ps) contel0 fields = do

  -- Andreas, 2022-10-06, issue #6165:
  -- The target type of the constructor is a meaningless dummy expression which does not type-check.
  -- We replace it by Set/Type (builtinSet) which is still incorrect but type-checks.
  -- It will be fixed after type-checking.
  aType <- A.Def . fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSet
  let contel = A.unPiView . (\ (A.PiView tels _) -> A.PiView tels aType) . A.piView $ contel0

  traceCall (CheckRecDef (getRange name) name ps fields) $ do
    reportSDoc "tc.rec" 10 $ vcat
      [ "checking record def" <+> prettyTCM name
      , nest 2 $ "ps ="     <+> prettyList (map prettyA ps)
      , nest 2 $ "contel =" <+> prettyA contel
      , nest 2 $ "fields =" <+> prettyA (map Constr fields)
      ]
    -- get type of record
    def <- instantiateDef =<< getConstInfo name
    t   <- instantiateFull $ defType def
    let npars =
          case theDef def of
            DataOrRecSig n -> n
            _              -> __IMPOSSIBLE__

    -- If the record type is erased, then hard compile-time mode is
    -- entered.
    setHardCompileTimeModeIfErased' def $ do

    parNames <- getGeneralizedParameters gpars name

    bindGeneralizedParameters parNames t $ \ gtel t0 ->
     bindParameters (npars - length parNames) ps t0 $ \ ptel t0 -> do

      let tel = abstract gtel ptel

      -- Generate type of constructor from field telescope @contel@,
      -- which is the approximate constructor type (target missing).

      -- Check and evaluate field types.
      reportSDoc "tc.rec" 15 $ "checking fields"
      contype <- workOnTypes $ instantiateFull =<< isType_ contel
      reportSDoc "tc.rec" 20 $ vcat
        [ "contype = " <+> prettyTCM contype ]

      -- compute the field telescope (does not include record parameters)
      let TelV ftel _ = telView' contype

      -- Compute correct type of constructor

      -- t = tel -> t0 where t0 must be a sort s
      TelV idxTel s <- telView t0
      unless (null idxTel) $ typeError $ ShouldBeASort t0
      s <- forceSort s

      -- needed for impredicative Prop (not implemented yet)
      -- ftel <- return $
      --   if s == Prop
      --   then telFromList $ map (setRelevance Irrelevant) $ telToList ftel
      --   else ftel

      reportSDoc "tc.rec" 20 $ do
        gamma <- getContextTelescope  -- the record params (incl. module params)
        "gamma = " <+> inTopContext (prettyTCM gamma)

      -- record type (name applied to parameters)
      rect <- El s . Def name . map Apply <$> getContextArgs

      -- Put in @rect@ as correct target of constructor type.
      -- Andreas, 2011-05-10 use telePi_ instead of telePi to preserve
      -- even names of non-dependent fields in constructor type (Issue 322).
      let contype = telePi_ ftel (raise (size ftel) rect)
        -- NB: contype does not contain the parameter telescope

      -- Obtain name of constructor (if present).
      (hasNamedCon, conName) <- case con of
        Just c  -> return (True, c)
        Nothing -> do
          m <- killRange <$> currentModule
          -- Andreas, 2020-06-01, AIM XXXII
          -- Using prettyTCM here jinxes the printer, see PR #4699.
          -- r <- prettyTCM name
          let r = P.pretty $ qnameName name
          c <- qualify m <$> freshName_ (render r ++ ".constructor")
          return (False, c)

      -- Add record type to signature.
      reportSDoc "tc.rec" 15 $ "adding record type to signature"

      etaenabled <- etaEnabled

      let getName :: A.Declaration -> [Dom QName]
          getName (A.Field _ x arg)    = [x <$ domFromArg arg]
          getName (A.ScopedDecl _ [f]) = getName f
          getName _                    = []

          setTactic dom f = f { domTactic = domTactic dom }

          fs = zipWith setTactic (telToList ftel) $ concatMap getName fields

          -- indCo is what the user wrote: inductive/coinductive/Nothing.
          -- We drop the Range.
          indCo = rangedThing <$> ind
          -- A constructor is inductive unless declared coinductive.
          conInduction = fromMaybe Inductive indCo
          -- Andreas, 2016-09-20, issue #2197.
          -- Eta is inferred by the positivity checker.
          -- We should turn it off until it is proven to be safe.
          haveEta      = maybe (Inferred $ NoEta patCopat) Specified eta
          -- haveEta      = maybe (Inferred $ conInduction == Inductive && etaenabled) Specified eta
          con = ConHead conName (IsRecord patCopat) conInduction $ map argFromDom fs

          -- A record is irrelevant if all of its fields are.
          -- In this case, the associated module parameter will be irrelevant.
          -- See issue 392.
          -- Unless it's been declared coinductive or no-eta-equality (#2607).
          recordRelevance
            | Just NoEta{} <- eta         = Relevant
            | CoInductive <- conInduction = Relevant
            | otherwise                   = minimum $ Irrelevant : map getRelevance (telToList ftel)

      -- Andreas, 2017-01-26, issue #2436
      -- Disallow coinductive records with eta-equality
      when (conInduction == CoInductive && theEtaEquality haveEta == YesEta) $ do
        typeError . GenericDocError =<< do
          sep [ "Agda doesn't like coinductive records with eta-equality."
              , "If you must, use pragma"
              , "{-# ETA" <+> prettyTCM name <+> "#-}"
              ]
      reportSDoc "tc.rec" 30 $ "record constructor is " <+> prettyTCM con

      -- Jesper, 2021-05-26: Warn when declaring coinductive record
      -- but neither --guardedness nor --sized-types is enabled.
      when (conInduction == CoInductive) $ do
        unlessM ((optGuardedness || optSizedTypes || optTypeBasedTermination) <$> pragmaOptions) $
          warning $ NoGuardednessFlag name

      -- Add the record definition.

      -- Andreas, 2016-06-17, Issue #2018:
      -- Do not rely on @addConstant@ to put in the record parameters,
      -- as they might be renamed in the context.
      -- By putting them ourselves (e.g. by using the original type @t@)
      -- we make sure we get the original names!
      let npars = size tel
          telh  = fmap hideAndRelParams tel
      escapeContext impossible npars $ do
        addConstant' name defaultArgInfo name t $
            Record
              { recPars           = npars
              , recClause         = Nothing
              , recConHead        = con
              , recNamedCon       = hasNamedCon
              , recFields         = fs
              , recTel            = telh `abstract` ftel
              , recAbstr          = Info.defAbstract i
              , recEtaEquality'   = haveEta
              , recPatternMatching= patCopat
              , recInduction      = indCo
                  -- We retain the original user declaration [(co)inductive]
                  -- in case the record turns out to be recursive.
              -- Determined by positivity checker:
              , recMutual         = Nothing
              -- Determined by the termination checker:
              , recTerminates     = Nothing
              , recComp           = emptyCompKit -- filled in later
              }

        erasure <- optErasure <$> pragmaOptions
        -- Add record constructor to signature
        addConstant' conName defaultArgInfo conName
             -- If --erasure is used, then the parameters are erased
             -- in the constructor's type.
            (applyWhen erasure (fmap $ applyQuantity zeroQuantity) telh
             `abstract` contype) $
            Constructor
              { conPars   = npars
              , conArity  = size fs
              , conSrcCon = con
              , conData   = name
              , conAbstr  = Info.defAbstract i
              , conComp   = emptyCompKit  -- filled in later
              , conProj   = Nothing       -- filled in later
              , conForced = []
              , conErased = Nothing
              , conErasure = erasure
              , conInline  = False
              }

      -- Declare the constructor as eligible for instance search
      case Info.defInstance i of
        InstanceDef r -> setCurrentRange r $ do
          -- Andreas, 2020-01-28, issue #4360:
          -- Use addTypedInstance instead of addNamedInstance
          -- to detect unusable instances.
          addTypedInstance conName contype
          -- addNamedInstance conName name
        NotInstanceDef -> pure ()

      -- Check that the fields fit inside the sort
      _ <- fitsIn conName uc [] contype s

      -- Check that the sort admits record declarations.
      checkDataSort name s


      {- Andreas, 2011-04-27 WRONG because field types are checked again
         and then non-stricts should not yet be irrelevant

      -- make record parameters hidden and non-stricts irrelevant
      -- ctx <- (reverse . map hideAndRelParams . take (size tel)) <$> getContext
      -}

{- Andreas, 2013-09-13 DEBUGGING the debug printout
      reportSDoc "tc.rec" 80 $ sep
        [ "current module record telescope"
        , nest 2 $ (prettyTCM =<< getContextTelescope)
        ]
      reportSDoc "tc.rec" 80 $ sep
        [ "current module record telescope"
        , nest 2 $ (text . show =<< getContextTelescope)
        ]
      reportSDoc "tc.rec" 80 $ sep
        [ "current module record telescope"
        , nest 2 $ (inTopContext . prettyTCM =<< getContextTelescope)
        ]
      reportSDoc "tc.rec" 80 $ sep
        [ "current module record telescope"
        , nest 2 $ do
           tel <- getContextTelescope
           text (show tel) $+$ do
           inTopContext $ do
             prettyTCM tel $+$ do
               telA <- reify tel
               text (show telA) $+$ do
               ctx <- getContextTelescope
               "should be empty:" <+> prettyTCM ctx
        ]
-}

      let info = setRelevance recordRelevance defaultArgInfo
          addRecordVar =
            addRecordNameContext (setArgInfo info $ defaultDom rect)

      let m = qnameToMName name  -- Name of record module.

      eraseRecordParameters <- optEraseRecordParameters <$> pragmaOptions
      let maybeErase :: forall a. LensQuantity a => a -> a
          maybeErase | eraseRecordParameters = setQuantity zeroQuantity
                     | otherwise             = id

      -- Andreas, 2016-02-09 setting all parameters hidden in the record
      -- section telescope changes the semantics, see e.g.
      -- test/Succeed/RecordInParModule.
      -- Ulf, 2016-03-02 but it's the right thing to do (#1759)
      modifyContextInfo (hideOrKeepInstance . maybeErase) $ addRecordVar $ do

        -- Add the record section.

        reportSDoc "tc.rec.def" 10 $ sep
          [ "record section:"
          , nest 2 $ sep
            [ prettyTCM m <+> (inTopContext . prettyTCM =<< getContextTelescope)
            , fsep $ punctuate comma $ map (return . P.pretty . map argFromDom . getName) fields
            ]
          ]
        reportSDoc "tc.rec.def" 15 $ nest 2 $ vcat
          [ "field tel =" <+> escapeContext impossible 1 (prettyTCM ftel)
          ]
        addSection m

      -- Andreas, 2016-02-09, Issue 1815 (see also issue 1759).
      -- For checking the record declarations, hide the record parameters
      -- and the parameters of the parent modules.
      modifyContextInfo (hideOrKeepInstance . maybeErase) $ do
        -- If --erasure is used, then the parameters are erased in the
        -- types of the projections.
        erasure <- optErasure <$> pragmaOptions
        params  <- applyWhen erasure (fmap $ applyQuantity zeroQuantity) <$> getContext

        -- Check the types of the fields and the other record declarations.
        addRecordVar $ withCurrentModule m $ do

          -- Andreas, 2013-09-13, 2016-01-06.
          -- Argument telescope for the projections: all parameters are hidden.
          -- This means parameters of the parent modules and of the current
          -- record type.
          -- See test/Succeed/ProjectionsTakeModuleTelAsParameters.agda.
          tel' <- do
            r <- headWithDefault __IMPOSSIBLE__ <$> getContext
            return $ telFromList' nameToArgName $ reverse $ r : params
          setModuleCheckpoint m
          checkRecordProjections m name hasNamedCon con tel' ftel fields


      -- we define composition here so that the projections are already in the signature.
      whenM (optCubicalCompatible <$> pragmaOptions) do
        escapeContext impossible npars do
          addCompositionForRecord name haveEta con tel (map argFromDom fs) ftel rect

      -- The confluence checker needs to know what symbols match against
      -- the constructor.
      modifySignature $ updateDefinition conName $ \def ->
        def { defMatchable = Set.fromList $ map unDom fs }

  where
  -- Andreas, 2020-04-19, issue #4560
  -- If the user declared the record constructor as @pattern@,
  -- then switch on pattern matching for no-eta-equality.
  -- Default is no pattern matching, but definition by copatterns instead.
  patCopat = maybe CopatternMatching (const PatternMatching) pat
  eta      = (patCopat <$) <$> eta0


addCompositionForRecord
  :: QName       -- ^ Datatype name.
  -> EtaEquality
  -> ConHead
  -> Telescope   -- ^ @Γ@ parameters.
  -> [Arg QName] -- ^ Projection names.
  -> Telescope   -- ^ @Γ ⊢ Φ@ field types.
  -> Type        -- ^ @Γ ⊢ T@ target type.
  -> TCM ()
addCompositionForRecord name eta con tel fs ftel rect = do
  cxt <- getContextTelescope
  inTopContext $ do

    -- Record has no fields: attach composition data to record constructor
    if null fs then do
      kit <- defineCompData name con (abstract cxt tel) [] ftel rect []
      modifySignature $ updateDefinition (conName con) $ updateTheDef $ \case
        r@Constructor{} -> r { conComp = kit, conProj = Just [] }  -- no projections
        _ -> __IMPOSSIBLE__

    -- No-eta record with pattern matching (i.e., withOUT copattern
    -- matching): define composition as for a data type, attach it to
    -- the record.
    else if theEtaEquality eta == NoEta PatternMatching then do
      kit <- defineCompData name con (abstract cxt tel) (unArg <$> fs) ftel rect []
      modifySignature $ updateDefinition name $ updateTheDef $ \case
        r@Record{} -> r { recComp = kit }
        _ -> __IMPOSSIBLE__

    -- Record has fields: attach composition data to record type
    else do
      -- If record has irrelevant fields but irrelevant projections are disabled,
      -- we cannot generate composition data.
      kit <- ifM (return (any isIrrelevant fs)
                  `and2M` do not . optIrrelevantProjections <$> pragmaOptions)
        {-then-} (return emptyCompKit)
        {-else-} (defineCompKitR name (abstract cxt tel) ftel fs rect)
      modifySignature $ updateDefinition name $ updateTheDef $ \case
        r@Record{} -> r { recComp = kit }
        _          -> __IMPOSSIBLE__

defineCompKitR ::
    QName          -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM CompKit
defineCompKitR name params fsT fns rect = do
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
  reportSDoc "tc.rec.cxt" 30 $ prettyTCM params
  reportSDoc "tc.rec.cxt" 30 $ prettyTCM fsT
  reportSDoc "tc.rec.cxt" 30 $ pretty rect
  if not $ all isJust required then return $ emptyCompKit else do
    transp <- whenDefined [builtinTrans]              (defineKanOperationR DoTransp name params fsT fns rect)
    hcomp  <- whenDefined [builtinTrans,builtinHComp] (defineKanOperationR DoHComp name params fsT fns rect)
    return $ CompKit
      { nameOfTransp = transp
      , nameOfHComp  = hcomp
      }
  where
    whenDefined xs m = do
      xs <- mapM getTerm' xs
      if all isJust xs then m else return Nothing


defineKanOperationR
  :: Command
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM (Maybe QName)
defineKanOperationR cmd name params fsT fns rect = do
  let project = (\ t fn -> t `applyE` [Proj ProjSystem fn])
  stuff <- fmap fst <$> defineKanOperationForFields cmd Nothing project name params fsT fns rect

  caseMaybe stuff (return Nothing) $ \ (theName, gamma, rtype, clause_types, bodies) -> do
  -- phi = 1 clause
  c' <- do
           io <- primIOne
           Just io_name <- getBuiltinName' builtinIOne
           one <- primItIsOne
           tInterval <- primIntervalType
           let
              (ix,rhs) =
                case cmd of
                  -- TranspRArgs = phi : I, a0 : ..
                  -- Γ = Δ^I , CompRArgs
                  -- pats = ... | phi = i1
                  -- body = a0
                  DoTransp -> (1,Var 0 [])
                  -- HCompRArgs = phi : I, u : .., a0 : ..
                  -- Γ = Δ, CompRArgs
                  -- pats = ... | phi = i1
                  -- body = u i1 itIsOne
                  DoHComp  -> (2,Var 1 [] `apply` [argN io, setRelevance Irrelevant $ argN one])

              p = ConP (ConHead io_name IsData Inductive [])
                       (noConPatternInfo { conPType = Just (Arg defaultArgInfo tInterval)
                                         , conPFallThrough = True })
                         []

              -- gamma, rtype

              s = singletonS ix p

              pats :: [NamedArg DeBruijnPattern]
              pats = s `applySubst` teleNamedArgs gamma

              t :: Type
              t = s `applyPatSubst` rtype

              gamma' :: Telescope
              gamma' = unflattenTel (ns0 ++ ns1) $ s `applyPatSubst` (g0 ++ g1)
               where
                (g0,_:g1) = splitAt (size gamma - 1 - ix) $ flattenTel gamma
                (ns0,_:ns1) = splitAt (size gamma - 1 - ix) $ teleNames gamma

              c = Clause { clauseFullRange = noRange
                         , clauseLHSRange  = noRange
                         , clauseTel       = gamma'
                         , namedClausePats = pats
                         , clauseBody      = Just $ rhs
                         , clauseType      = Just $ argN t
                         , clauseCatchall    = False
                         , clauseExact       = Just True
                         , clauseRecursive   = Just False  -- definitely non-recursive!
                         , clauseUnreachable = Just False
                         , clauseEllipsis    = NoEllipsis
                         , clauseWhereModule = Nothing
                         }
           reportSDoc "trans.rec.face" 17 $ text $ show c
           return c
  cs <- forM (zip3 fns clause_types bodies) $ \ (fname, clause_ty, body) -> do
          let
              pats = teleNamedArgs gamma ++ [defaultNamedArg $ ProjP ProjSystem $ unArg fname]
              c = Clause { clauseFullRange = noRange
                         , clauseLHSRange  = noRange
                         , clauseTel       = gamma
                         , namedClausePats = pats
                         , clauseBody      = Just body
                         , clauseType      = Just $ argN (unDom clause_ty)
                         , clauseCatchall    = False
                         , clauseExact       = Just True
                         , clauseRecursive   = Nothing
                             -- Andreas 2020-02-06 TODO
                             -- Or: Just False;  is it known to be non-recursive?
                         , clauseUnreachable = Just False
                         , clauseEllipsis    = NoEllipsis
                         , clauseWhereModule = Nothing
                         }
          reportSDoc "trans.rec" 17 $ text $ show c
          reportSDoc "trans.rec" 16 $ text "type =" <+> text (show (clauseType c))
          reportSDoc "trans.rec" 15 $ prettyTCM $ abstract gamma (unDom clause_ty)
          reportSDoc "trans.rec" 10 $ text "body =" <+> prettyTCM (abstract gamma body)
          return c
  addClauses theName $ c' : cs
  reportSDoc "trans.rec" 15 $ text $ "compiling clauses for " ++ show theName
  (mst, _, cc) <- inTopContext (compileClauses Nothing cs)
  whenJust mst $ setSplitTree theName
  setCompiledClauses theName cc
  reportSDoc "trans.rec" 15 $ text $ "compiled"
  return $ Just theName


{-| @checkRecordProjections m r q tel ftel fs@.

    [@m@    ]  name of the generated module

    [@r@    ]  name of the record type

    [@con@  ]  name of the record constructor

    [@tel@  ]  parameters (perhaps erased) and record variable r ("self")

    [@ftel@ ]  telescope of fields

    [@fs@   ]  the fields to be checked
-}
checkRecordProjections ::
  ModuleName -> QName -> Bool -> ConHead -> Telescope -> Telescope ->
  [A.Declaration] -> TCM ()
checkRecordProjections m r hasNamedCon con tel ftel fs = do
    checkProjs EmptyTel ftel [] fs
  where

    checkProjs :: Telescope -> Telescope -> [Term] -> [A.Declaration] -> TCM ()

    checkProjs _ _ _ [] = return ()

    checkProjs ftel1 ftel2 vs (A.ScopedDecl scope fs' : fs) =
      setScope scope >> checkProjs ftel1 ftel2 vs (fs' ++ fs)

    -- Case: projection.
    checkProjs ftel1 (ExtendTel (dom@Dom{domInfo = ai,unDom = t}) ftel2) vs (A.Field info x _ : fs) =
      traceCall (CheckProjection (getRange info) x t) $ do
      -- Andreas, 2012-06-07:
      -- Issue 387: It is wrong to just type check field types again
      -- because then meta variables are created again.
      -- Instead, we take the field type t from the field telescope.
      reportSDoc "tc.rec.proj" 5 $ sep
        [ "checking projection" <+> prettyTCM x
        , nest 2 $ vcat
          [ "top   =" <+> (inTopContext . prettyTCM =<< getContextTelescope)
          , "tel   =" <+> (inTopContext . prettyTCM $ tel)
          ]
        ]
      -- Andreas, 2021-05-11, issue #5378
      -- The impossible is sometimes possible, so splitting out this part...
      reportSDoc "tc.rec.proj" 5 $ nest 2 $ vcat
          [ "ftel1 =" <+> escapeContext impossible 1 (prettyTCM ftel1)
          , "t     =" <+> escapeContext impossible 1 (addContext ftel1 $ prettyTCM t)
          , "ftel2 =" <+> escapeContext impossible 1 (addContext ftel1 $ underAbstraction dom ftel2 prettyTCM)
          ]
      reportSDoc "tc.rec.proj" 55 $ nest 2 $ vcat
          [ "ftel1 (raw) =" <+> pretty ftel1
          , "t     (raw) =" <+> pretty t
          , "ftel2 (raw) =" <+> pretty ftel2
          ]
      reportSDoc "tc.rec.proj" 5 $ nest 2 $ vcat
          [ "vs    =" <+> prettyList_ (map prettyTCM vs)
          , "abstr =" <+> (text . show) (Info.defAbstract info)
          , "quant =" <+> (text . show) (getQuantity ai)
          , "coh   =" <+> (text . show) (getCohesion ai)
          ]

      -- Cohesion check:
      -- For a field `@c π : A` we would create a projection `π : .., (@(c^-1) r : R as) -> A`
      -- So we want to check that `@.., (c^-1 . c) x : A |- x : A` is allowed by the modalities.
      --
      -- Alternatively we could create a projection `.. |- π r :c A`
      -- but that would require support for a `t :c A` judgment.
      if hasLeftAdjoint (UnderComposition (getCohesion ai))
        then unless (getCohesion ai == Continuous)
                    -- Andrea TODO: properly update the context/type of the projection when we add Sharp
                    __IMPOSSIBLE__
        else genericError $ "Cannot have record fields with modality " ++ show (getCohesion ai)

      -- The telescope tel includes the variable of record type as last one
      -- e.g. for cartesion product it is
      --
      --   tel = {A' : Set} {B' : Set} (r : Prod A' B')

      -- create the projection functions (instantiate the type with the values
      -- of the previous fields)

      -- The type of the projection function should be
      --  {Δ} -> (r : R Δ) -> t
      -- where Δ are the parameters of R

      {- what are the contexts?

          Δ , ftel₁              ⊢ t
          Δ , (r : R Δ)          ⊢ parallelS vs : ftel₁
          Δ , (r : R Δ) , ftel₁  ⊢ t' = raiseFrom (size ftel₁) 1 t
          Δ , (r : R Δ)          ⊢ t'' = applySubst (parallelS vs) t'
                                 ⊢ finalt = telePi tel t''
      -}
      let t'       = raiseFrom (size ftel1) 1 t
          t''      = applySubst (parallelS vs) t'
          finalt   = telePi (replaceEmptyName "r" tel) t''
          projname = qualify m $ qnameName x
          projcall o = Var 0 [Proj o projname]
          rel      = getRelevance ai
          -- the recursive call
          recurse  = checkProjs (abstract ftel1 $ ExtendTel dom
                                 $ Abs (nameToArgName $ qnameName projname) EmptyTel)
                                (absBody ftel2) (projcall ProjSystem : vs) fs

      reportSDoc "tc.rec.proj" 25 $ nest 2 $ "finalt=" <+> do
        inTopContext $ prettyTCM finalt

      -- -- Andreas, 2012-02-20 do not add irrelevant projections if
      -- -- disabled by --no-irrelevant-projections
      -- ifM (return (rel == Irrelevant) `and2M` do not . optIrrelevantProjections <$> pragmaOptions) recurse $ do
      -- Andreas, 2018-06-09 issue #2170
      -- Always create irrelevant projections (because the scope checker accepts irrelevant fields).
      -- If --no-irrelevant-projections, then their use should be disallowed by the type checker for expressions.
      do
        reportSDoc "tc.rec.proj" 10 $ sep
          [ "adding projection"
          , nest 2 $ prettyTCM projname <+> ":" <+> inTopContext (prettyTCM finalt)
          ]

        -- The body should be
        --  P.xi {tel} (r _ .. x .. _) = x
        -- Ulf, 2011-08-22: actually we're dropping the parameters from the
        -- projection functions so the body is now
        --  P.xi (r _ .. x .. _) = x
        -- Andreas, 2012-01-12: irrelevant projections get translated to
        --  P.xi (r _ .. x .. _) = irrAxiom {level of t} {t} x
        -- PROBLEM: because of dropped parameters, cannot refer to t
        -- 2012-04-02: DontCare instead of irrAxiom

        -- compute body modification for irrelevant projections
        let bodyMod = case rel of
              Relevant   -> id
              NonStrict  -> id
              Irrelevant -> dontCare

        let -- Andreas, 2010-09-09: comment for existing code
            -- split the telescope into parameters (ptel) and the type or the record
            -- (rt) which should be  R ptel
            telList = telToList tel
            (ptelList,[rt]) = splitAt (size tel - 1) telList
            ptel   = telFromList ptelList
            cpo    = if hasNamedCon then PatOCon else PatORec
            cpi    = ConPatternInfo { conPInfo   = PatternInfo cpo []
                                    , conPRecord = True
                                    , conPFallThrough = False
                                    , conPType   = Just $ argFromDom $ fmap snd rt
                                    , conPLazy   = True }
            conp   = defaultNamedArg $ ConP con cpi $ teleNamedArgs ftel
            body   = Just $ bodyMod $ var (size ftel2)
            cltel  = ptel `abstract` ftel
            cltype = Just $ Arg ai $ raise (1 + size ftel2) t
            clause = Clause { clauseLHSRange  = getRange info
                            , clauseFullRange = getRange info
                            , clauseTel       = killRange cltel
                            , namedClausePats = [conp]
                            , clauseBody      = body
                            , clauseType      = cltype
                            , clauseCatchall  = False
                            , clauseExact       = Just True
                            , clauseRecursive   = Just False
                            , clauseUnreachable = Just False
                            , clauseEllipsis    = NoEllipsis
                            , clauseWhereModule = Nothing
                            }

        let projection = Projection
              { projProper   = Just r
              , projOrig     = projname
              -- name of the record type:
              , projFromType = defaultArg r
              -- index of the record argument (in the type),
              -- start counting with 1:
              , projIndex    = size tel -- which is @size ptel + 1@
              , projLams     = ProjLams $ map (argFromDom . fmap fst) telList
              }

        reportSDoc "tc.rec.proj" 70 $ sep
          [ "adding projection"
          , nest 2 $ prettyTCM projname <+> pretty clause
          ]
        reportSDoc "tc.rec.proj" 10 $ sep
          [ "adding projection"
          , nest 2 $ prettyTCM (QNamed projname clause)
          ]

              -- Record patterns should /not/ be translated when the
              -- projection functions are defined. Record pattern
              -- translation is defined in terms of projection
              -- functions.
        (mst, _, cc) <- compileClauses Nothing [clause]

        reportSDoc "tc.cc" 60 $ do
          sep [ "compiled clauses of " <+> prettyTCM projname
              , nest 2 $ text (show cc)
              ]

        escapeContext impossible (size tel) $ do
          lang <- getLanguage
          fun  <- emptyFunctionData
          let -- It should be fine to mark a field with @ω in an
              -- erased record type: the field will be non-erased, but
              -- the projection will be erased. The following code
              -- ensures that the use of addConstant does not trigger
              -- a PlentyInHardCompileTimeMode warning.
              ai' = flip mapQuantity ai $ \case
                      Quantityω _ -> Quantityω QωInferred
                      q           -> q
          addConstant projname $
            (defaultDefn ai' projname (killRange finalt) lang $ FunctionDefn
              fun
                { _funClauses        = [clause]
                , _funCompiled       = Just cc
                , _funSplitTree      = mst
                , _funProjection     = Right projection
                , _funMutual         = Just []  -- Projections are not mutually recursive with anything
                , _funTerminates     = Just True
                })
              { defArgOccurrences = [StrictPos]
              , defCopatternLHS   = hasProjectionPatterns cc
              }
          computePolarity [projname]

        case Info.defInstance info of
          -- fields do not have an @instance@ keyword!?
          InstanceDef _r -> addTypedInstance projname t
          NotInstanceDef -> pure ()

        recurse

    -- Case: definition.
    checkProjs ftel1 ftel2 vs (d : fs) = do
      checkDecl d
      checkProjs ftel1 ftel2 vs fs
