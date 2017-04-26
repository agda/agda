{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Record where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad
import Data.Maybe
import qualified Data.Set as Set

import Agda.Interaction.Options

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.CompiledClause.Compile

import Agda.TypeChecking.Rules.Data ( bindParameters, fitsIn, forceSort)
import Agda.TypeChecking.Rules.Term ( isType_ )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkDecl)

import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "undefined.h"
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
--     [@contel@]  Approximate type of constructor (@fields@ -> Set).
--                 Does not include record parameters.
--
--     [@fields@]  List of field signatures.
--
checkRecDef
  :: Info.DefInfo              -- ^ Position and other info.
  -> QName                     -- ^ Record type identifier.
  -> Maybe (Ranged Induction)  -- ^ Optional: (co)inductive declaration.
  -> Maybe Bool                -- ^ Optional: user specified eta/no-eta
  -> Maybe QName               -- ^ Optional: constructor name.
  -> [A.LamBinding]            -- ^ Record parameters.
  -> A.Expr                    -- ^ Approximate type of constructor (@fields@ -> Set).
                               --   Does not include record parameters.
  -> [A.Field]                 -- ^ Field signatures.
  -> TCM ()
checkRecDef i name ind eta con ps contel fields =
  traceCall (CheckRecDef (getRange name) (qnameName name) ps fields) $ do
    reportSDoc "tc.rec" 10 $ vcat
      [ text "checking record def" <+> prettyTCM name
      , nest 2 $ text "ps ="     <+> prettyList (map prettyAs ps)
      , nest 2 $ text "contel =" <+> prettyA contel
      , nest 2 $ text "fields =" <+> prettyA (map Constr fields)
      ]
    -- get type of record
    t <- instantiateFull =<< typeOfConst name
    bindParameters ps t $ \tel t0 -> do

      -- Generate type of constructor from field telescope @contel@,
      -- which is the approximate constructor type (target missing).

      -- Check and evaluate field types.
      reportSDoc "tc.rec" 15 $ text "checking fields"
      -- WRONG: contype <- workOnTypes $ killRange <$> (instantiateFull =<< isType_ contel)
      contype <- instantiateFull =<< isType_ contel
      reportSDoc "tc.rec" 20 $ vcat
        [ text "contype = " <+> prettyTCM contype ]

      -- compute the field telescope (does not include record parameters)
      let TelV ftel _ = telView' contype

          -- A record is irrelevant if all of its fields are.
          -- In this case, the associated module parameter will be irrelevant.
          -- See issue 392.
          recordRelevance = minimum $ Irrelevant : (map getRelevance $ telToList ftel)

      -- Compute correct type of constructor

      -- t = tel -> t0 where t0 must be a sort s
      TelV idxTel s <- telView t0
      unless (null idxTel) $ typeError $ ShouldBeASort t0
      s <- forceSort s

      reportSDoc "tc.rec" 20 $ do
        gamma <- getContextTelescope  -- the record params (incl. module params)
        text "gamma = " <+> inTopContext (prettyTCM gamma)

      -- record type (name applied to parameters)
      rect <- El s . Def name . map Apply <$> getContextArgs

      -- Put in @rect@ as correct target of constructor type.
      -- Andreas, 2011-05-10 use telePi_ instead of telePi to preserve
      -- even names of non-dependent fields in constructor type (Issue 322).
      let contype = telePi_ ftel (raise (size ftel) rect)
        -- NB: contype does not contain the parameter telescope

      -- Obtain name of constructor (if present).
      (hasNamedCon, conName, conInfo) <- case con of
        Just c  -> return (True, c, i)
        Nothing -> do
          m <- killRange <$> currentModule
          c <- qualify m <$> freshName_ ("recCon-NOT-PRINTED" :: String)
          return (False, c, i)

      -- Add record type to signature.
      reportSDoc "tc.rec" 15 $ text "adding record type to signature"

      etaenabled <- etaEnabled

      let getName :: A.Declaration -> [Arg QName]
          getName (A.Field _ x arg)    = [x <$ arg]
          getName (A.ScopedDecl _ [f]) = getName f
          getName _                    = []

          fs = concatMap getName fields
          -- indCo is what the user wrote: inductive/coinductive/Nothing.
          -- We drop the Range.
          indCo = rangedThing <$> ind
          -- A constructor is inductive unless declared coinductive.
          conInduction = fromMaybe Inductive indCo
          -- Andreas, 2016-09-20, issue #2197.
          -- Eta is inferred by the positivity checker.
          -- We should turn it off until it is proven to be safe.
          haveEta      = maybe (Inferred False) Specified eta
          -- haveEta      = maybe (Inferred $ conInduction == Inductive && etaenabled) Specified eta
          con = ConHead conName conInduction $ map unArg fs

      -- Andreas, 2017-01-26, issue #2436
      -- Disallow coinductive records with eta-equality
      when (conInduction == CoInductive && etaEqualityToBool haveEta == True) $ do
        typeError . GenericDocError =<< do
          sep [ text "Agda doesn't like coinductive records with eta-equality."
              , text "If you must, use pragma"
              , text "{-# ETA" <+> prettyTCM name <+> text "#-}"
              ]
      reportSDoc "tc.rec" 30 $ text "record constructor is " <+> text (show con)

      -- Add the record definition.

      -- Andreas, 2016-06-17, Issue #2018:
      -- Do not rely on @addConstant@ to put in the record parameters,
      -- as they might be renamed in the context.
      -- By putting them ourselves (e.g. by using the original type @t@)
      -- we make sure we get the original names!
      let npars = size tel
          telh  = fmap hideAndRelParams tel
      escapeContext npars $ do
        addConstant name $
          defaultDefn defaultArgInfo name t $
            Record
              { recPars           = npars
              , recClause         = Nothing
              , recConHead        = con
              , recNamedCon       = hasNamedCon
              , recFields         = fs
              , recTel            = telh `abstract` ftel
              , recAbstr          = Info.defAbstract i
              , recEtaEquality'   = haveEta
              , recInduction      = indCo
                  -- We retain the original user declaration [(co)inductive]
                  -- in case the record turns out to be recursive.
              -- Determined by positivity checker:
              , recMutual         = Nothing
              }

        -- Add record constructor to signature
        addConstant conName $
          defaultDefn defaultArgInfo conName (telh `abstract` contype) $
            Constructor
              { conPars   = npars
              , conArity  = size fs
              , conSrcCon = con
              , conData   = name
              , conAbstr  = Info.defAbstract conInfo
              , conInd    = conInduction
              , conErased = []
              }

      -- Declare the constructor as eligible for instance search
      when (Info.defInstance i == InstanceDef) $ do
        addNamedInstance conName name

      -- Check that the fields fit inside the sort
      _ <- contype `fitsIn` s

      {- Andreas, 2011-04-27 WRONG because field types are checked again
         and then non-stricts should not yet be irrelevant

      -- make record parameters hidden and non-stricts irrelevant
      -- ctx <- (reverse . map hideAndRelParams . take (size tel)) <$> getContext
      -}

{- Andreas, 2013-09-13 DEBUGGING the debug printout
      reportSDoc "tc.rec" 80 $ sep
        [ text "current module record telescope"
        , nest 2 $ (prettyTCM =<< getContextTelescope)
        ]
      reportSDoc "tc.rec" 80 $ sep
        [ text "current module record telescope"
        , nest 2 $ (text . show =<< getContextTelescope)
        ]
      reportSDoc "tc.rec" 80 $ sep
        [ text "current module record telescope"
        , nest 2 $ (inTopContext . prettyTCM =<< getContextTelescope)
        ]
      reportSDoc "tc.rec" 80 $ sep
        [ text "current module record telescope"
        , nest 2 $ do
           tel <- getContextTelescope
           text (show tel) $+$ do
           inTopContext $ do
             prettyTCM tel $+$ do
               telA <- reify tel
               text (show telA) $+$ do
               ctx <- getContextTelescope
               text "should be empty:" <+> prettyTCM ctx
        ]
-}

      let info = setRelevance recordRelevance defaultArgInfo
          addRecordVar = addContext' ("", Dom info rect)
          -- the record variable has the empty name by intention, see issue 208

      let m = qnameToMName name  -- Name of record module.

      -- Andreas, 2016-02-09 setting all parameters hidden in the record
      -- section telescope changes the semantics, see e.g.
      -- test/Succeed/RecordInParModule.
      -- Ulf, 2016-03-02 but it's the right thing to do (#1759)
      modifyContext (modifyContextEntries hideOrKeepInstance) $ addRecordVar $ do

        -- Add the record section.

        reportSDoc "tc.rec.def" 10 $ sep
          [ text "record section:"
          , nest 2 $ sep
            [ prettyTCM m <+> (inTopContext . prettyTCM =<< getContextTelescope)
            , fsep $ punctuate comma $ map (text . show . getName) fields
            ]
          ]
        reportSDoc "tc.rec.def" 15 $ nest 2 $ vcat
          [ text "field tel =" <+> escapeContext 1 (prettyTCM ftel)
          ]
        addSection m

      -- Andreas, 2016-02-09, Issue 1815 (see also issue 1759).
      -- For checking the record declarations, hide the record parameters
      -- and the parameters of the parent modules.
      modifyContext (modifyContextEntries hideOrKeepInstance) $ addRecordVar $ do

        -- Check the types of the fields and the other record declarations.
        withCurrentModule m $ do

          -- Andreas, 2013-09-13, 2016-01-06.
          -- Argument telescope for the projections: all parameters are hidden.
          -- This means parameters of the parent modules and of the current
          -- record type.
          -- See test/Succeed/ProjectionsTakeModuleTelAsParameters.agda.
          tel' <- getContextTelescope
          setDefaultModuleParameters m
          checkRecordProjections m name hasNamedCon con tel' (raise 1 ftel) fields

      return ()

{-| @checkRecordProjections m r q tel ftel fs@.

    [@m@    ]  name of the generated module

    [@r@    ]  name of the record type

    [@con@  ]  name of the record constructor

    [@tel@  ]  parameters and record variable r ("self")

    [@ftel@ ]  telescope of fields

    [@fs@   ]  the fields to be checked
-}
checkRecordProjections ::
  ModuleName -> QName -> Bool -> ConHead -> Telescope -> Telescope ->
  [A.Declaration] -> TCM ()
checkRecordProjections m r hasNamedCon con tel ftel fs = do
    checkProjs EmptyTel ftel fs
  where

    checkProjs :: Telescope -> Telescope -> [A.Declaration] -> TCM ()

    checkProjs _ _ [] = return ()

    checkProjs ftel1 ftel2 (A.ScopedDecl scope fs' : fs) =
      setScope scope >> checkProjs ftel1 ftel2 (fs' ++ fs)

    checkProjs ftel1 (ExtendTel (Dom ai t) ftel2) (A.Field info x _ : fs) =
      traceCall (CheckProjection (getRange info) x t) $ do
      -- Andreas, 2012-06-07:
      -- Issue 387: It is wrong to just type check field types again
      -- because then meta variables are created again.
      -- Instead, we take the field type t from the field telescope.
      reportSDoc "tc.rec.proj" 5 $ sep
        [ text "checking projection" <+> text (show x)
        , nest 2 $ vcat
          [ text "top   =" <+> (inTopContext . prettyTCM =<< getContextTelescope)
          , text "tel   =" <+> (inTopContext . prettyTCM $ tel)
          , text "ftel1 =" <+> prettyTCM ftel1
          , text "t     =" <+> prettyTCM t
          , text "ftel2 =" <+> addContext ftel1 (underAbstraction_ ftel2 prettyTCM)
          ]
        ]

      -- Andreas, 2010-09-09 The following comments are misleading, TODO: update
      -- in fact, tel includes the variable of record type as last one
      -- e.g. for cartesion product it is
      --
      --   tel = {A' : Set} {B' : Set} (r : Prod A' B')

      -- create the projection functions (instantiate the type with the values
      -- of the previous fields)

      {- what are the contexts?

          Γ, tel            ⊢ t
          Γ, tel, r         ⊢ vs
          Γ, tel, r, ftel₁  ⊢ raiseFrom (size ftel₁) 1 t
      -}

      -- The type of the projection function should be
      --  {tel} -> (r : R Δ) -> t
      -- where Δ = Γ, tel is the current context
      let finalt   = telePi (replaceEmptyName "r" tel) t
          projname = qualify m $ qnameName x
          projcall o = Var 0 [Proj o projname]
          rel      = getRelevance ai
          -- the recursive call
          recurse  = checkProjs (abstract ftel1 $ ExtendTel (Dom ai t)
                                 $ Abs (nameToArgName $ qnameName projname) EmptyTel)
                                (ftel2 `absApp` projcall ProjSystem) fs

      reportSDoc "tc.rec.proj" 25 $ nest 2 $ text "finalt=" <+> do
        inTopContext $ prettyTCM finalt

      -- Andreas, 2012-02-20 do not add irrelevant projections if
      -- disabled by --no-irrelevant-projections
      ifM (return (rel == Irrelevant) `and2M` do not . optIrrelevantProjections <$> pragmaOptions) recurse $ do

        reportSDoc "tc.rec.proj" 10 $ sep
          [ text "adding projection"
          , nest 2 $ prettyTCM projname <+> text ":" <+> inTopContext (prettyTCM finalt)
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
              Irrelevant -> DontCare
              _          -> __IMPOSSIBLE__

        let -- Andreas, 2010-09-09: comment for existing code
            -- split the telescope into parameters (ptel) and the type or the record
            -- (rt) which should be  R ptel
            telList = telToList tel
            (_ptel,[rt]) = splitAt (size tel - 1) telList
            cpo    = if hasNamedCon then ConOCon else ConORec
            cpi    = ConPatternInfo (Just cpo) (Just $ argFromDom $ fmap snd rt)
            conp   = defaultArg $ ConP con cpi $
                     [ Arg info $ unnamed $ varP "x" | Dom info _ <- telToList ftel ]
            body   = Just $ bodyMod $ var (size ftel2)
            cltel  = ftel
            clause = Clause { clauseLHSRange  = getRange info
                            , clauseFullRange = getRange info
                            , clauseTel       = killRange cltel
                            , namedClausePats = [Named Nothing <$> numberPatVars __IMPOSSIBLE__ (idP $ size ftel) conp]
                            , clauseBody      = body
                            , clauseType      = Just $ Arg ai t
                            , clauseCatchall  = False
                            }

        let projection = Projection
              { projProper   = Just r
              , projOrig     = projname
              -- name of the record type:
              , projFromType = defaultArg r
              -- index of the record argument (in the type),
              -- start counting with 1:
              , projIndex    = size tel -- which is @size ptel + 1@
              , projLams     = ProjLams $ map (\ (Dom ai (x,_)) -> Arg ai x) telList
              }

        reportSDoc "tc.rec.proj" 80 $ sep
          [ text "adding projection"
          , nest 2 $ prettyTCM projname <+> text (show clause)
          ]
        reportSDoc "tc.rec.proj" 70 $ sep
          [ text "adding projection"
          , nest 2 $ prettyTCM projname <+> text (show (clausePats clause)) <+> text "=" <+>
                       inTopContext (addContext ftel (maybe (text "_|_") prettyTCM (clauseBody clause)))
          ]
        reportSDoc "tc.rec.proj" 10 $ sep
          [ text "adding projection"
          , nest 2 $ prettyTCM (QNamed projname clause)
          ]

              -- Record patterns should /not/ be translated when the
              -- projection functions are defined. Record pattern
              -- translation is defined in terms of projection
              -- functions.
        cc <- compileClauses Nothing [clause]

        reportSDoc "tc.cc" 60 $ do
          sep [ text "compiled clauses of " <+> prettyTCM projname
              , nest 2 $ text (show cc)
              ]

        escapeContext (size tel) $ do
          addConstant projname $
            (defaultDefn ai projname (killRange finalt)
              emptyFunction
                { funClauses        = [clause]
                , funCompiled       = Just cc
                , funProjection     = Just projection
                , funTerminates     = Just True
                , funCopatternLHS   = isCopatternLHS [clause]
                })
              { defArgOccurrences = [StrictPos] }
          computePolarity [projname]
          when (Info.defInstance info == InstanceDef) $
            addTypedInstance projname finalt

        recurse

    checkProjs ftel1 ftel2 (d : fs) = do
      checkDecl d
      checkProjs ftel1 ftel2 fs
