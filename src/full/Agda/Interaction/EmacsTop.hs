module Agda.Interaction.EmacsTop
    ( mimicGHCi
    , showGoals
    ) where

import Control.Monad.State hiding (state)
import qualified Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Abstract.Pretty (prettyATop)
import Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete as C

import Agda.TypeChecking.Errors (prettyError)
import qualified Agda.TypeChecking.Pretty as TCP
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Pretty.Warning (prettyTCWarnings, prettyTCWarnings')
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Warnings (WarningsAndNonFatalErrors(..))
import Agda.Interaction.AgdaTop
import Agda.Interaction.BasicOps as B
import Agda.Interaction.Response as R
import Agda.Interaction.EmacsCommand hiding (putResponse)
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Precise (TokenBased(..))
import Agda.Interaction.InteractionTop (localStateCommandM)
import Agda.Interaction.Imports (getAllWarningsOfTCErr)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Null (empty)
import Agda.Utils.Maybe
import Agda.Utils.Pretty
import Agda.Utils.String
import Agda.Utils.Time (CPUTime)
import Agda.VersionCommit

----------------------------------

-- | 'mimicGHCi' is a fake ghci interpreter for the Emacs frontend
--   and for interaction tests.
--
--   'mimicGHCi' reads the Emacs frontend commands from stdin,
--   interprets them and print the result into stdout.
mimicGHCi :: TCM () -> TCM ()
mimicGHCi = repl (liftIO . mapM_ print <=< lispifyResponse) "Agda2> "

-- | Convert Response to an elisp value for the interactive emacs frontend.

lispifyResponse :: Response -> TCM [Lisp String]
lispifyResponse (Resp_HighlightingInfo info remove method modFile) =
  (:[]) <$> liftIO (lispifyHighlightingInfo info remove method modFile)
lispifyResponse (Resp_DisplayInfo info) = lispifyDisplayInfo info
lispifyResponse (Resp_ClearHighlighting tokenBased) =
  return [ L $ A "agda2-highlight-clear" :
               case tokenBased of
                 NotOnlyTokenBased -> []
                 TokenBased        ->
                   [ Q (lispifyTokenBased tokenBased) ]
         ]
lispifyResponse Resp_DoneAborting = return [ L [ A "agda2-abort-done" ] ]
lispifyResponse Resp_ClearRunningInfo = return [ clearRunningInfo ]
lispifyResponse (Resp_RunningInfo n s)
  | n <= 1    = return [ displayRunningInfo s ]
  | otherwise = return [ L [A "agda2-verbose", A (quote s)] ]
lispifyResponse (Resp_Status s)
    = return [ L [ A "agda2-status-action"
                 , A (quote $ List.intercalate "," $ catMaybes [checked, showImpl])
                 ]
             ]
  where
    checked  = boolToMaybe (sChecked               s) "Checked"
    showImpl = boolToMaybe (sShowImplicitArguments s) "ShowImplicit"

lispifyResponse (Resp_JumpToError f p) = return
  [ lastTag 3 $
      L [ A "agda2-maybe-goto", Q $ L [A (quote f), A ".", A (show p)] ]
  ]
lispifyResponse (Resp_InteractionPoints is) = return
  [ lastTag 1 $
      L [A "agda2-goals-action", Q $ L $ map showNumIId is]
  ]
lispifyResponse (Resp_GiveAction ii s)
    = return [ L [ A "agda2-give-action", showNumIId ii, A s' ] ]
  where
    s' = case s of
        Give_String str -> quote str
        Give_Paren      -> "'paren"
        Give_NoParen    -> "'no-paren"
lispifyResponse (Resp_MakeCase variant pcs) = return
  [ lastTag 2 $ L [ A cmd, Q $ L $ map (A . quote) pcs ] ]
  where
  cmd = case variant of
    R.Function       -> "agda2-make-case-action"
    R.ExtendedLambda -> "agda2-make-case-action-extendlam"
lispifyResponse (Resp_SolveAll ps) = return
  [ lastTag 2 $
      L [ A "agda2-solveAll-action", Q . L $ concatMap prn ps ]
  ]
  where
    prn (ii,e)= [showNumIId ii, A $ quote $ prettyShow e]

lispifyDisplayInfo :: DisplayInfo -> TCM [Lisp String]
lispifyDisplayInfo info = case info of
    Info_CompilationOk ws -> do
      warnings <- prettyTCWarnings (tcWarnings ws)
      errors <- prettyTCWarnings (nonFatalErrors ws)
      -- abusing the goals field since we ignore the title
      let (body, _) = formatWarningsAndErrors
                        "The module was successfully compiled.\n"
                        warnings
                        errors
      format body "*Compilation result*"
    Info_Constraints s -> format (show $ vcat $ map pretty s) "*Constraints*"
    Info_AllGoalsWarnings ms ws -> do
      goals <- showGoals ms
      warnings <- prettyTCWarnings (tcWarnings ws)
      errors <- prettyTCWarnings (nonFatalErrors ws)
      let (body, title) = formatWarningsAndErrors goals warnings errors
      format body ("*All" ++ title ++ "*")
    Info_Auto s -> format s "*Auto*"
    Info_Error err -> do
      s <- showInfoError err
      format s "*Error*"
    Info_Time s -> format (render $ prettyTimed s) "*Time*"
    Info_NormalForm state cmode time expr -> do
      exprDoc <- evalStateT prettyExpr state
      let doc = maybe empty prettyTimed time $$ exprDoc
      format (render doc) "*Normal Form*"
      where
        prettyExpr = localStateCommandM
            $ lift
            $ B.atTopLevel
            $ allowNonTerminatingReductions
            $ (if computeIgnoreAbstract cmode then ignoreAbstractMode else inConcreteMode)
            $ (B.showComputed cmode)
            $ expr
    Info_InferredType state time expr -> do
      exprDoc <- evalStateT prettyExpr state
      let doc = maybe empty prettyTimed time $$ exprDoc
      format (render doc) "*Inferred Type*"
      where
        prettyExpr = localStateCommandM
            $ lift
            $ B.atTopLevel
            $ TCP.prettyA
            $ expr
    Info_ModuleContents modules tel types -> do
      doc <- localTCState $ do
        typeDocs <- addContext tel $ forM types $ \ (x, t) -> do
          doc <- prettyTCM t
          return (prettyShow x, ":" <+> doc)
        return $ vcat
          [ "Modules"
          , nest 2 $ vcat $ map pretty modules
          , "Names"
          , nest 2 $ align 10 typeDocs
          ]
      format (render doc) "*Module contents*"
    Info_SearchAbout hits names -> do
      hitDocs <- forM hits $ \ (x, t) -> do
        doc <- prettyTCM t
        return (prettyShow x, ":" <+> doc)
      let doc = "Definitions about" <+>
                text (List.intercalate ", " $ words names) $$ nest 2 (align 10 hitDocs)
      format (render doc) "*Search About*"
    Info_WhyInScope s cwd v xs ms -> do
      doc <- explainWhyInScope s cwd v xs ms
      format (render doc) "*Scope Info*"
    Info_Context ii ctx -> do
      doc <- localTCState (prettyResponseContext ii False ctx)
      format (render doc) "*Context*"
    Info_Intro_NotFound -> format "No introduction forms found." "*Intro*"
    Info_Intro_ConstructorUnknown ss -> do
      let doc = sep [ "Don't know which constructor to introduce of"
                    , let mkOr []     = []
                          mkOr [x, y] = [text x <+> "or" <+> text y]
                          mkOr (x:xs) = text x : mkOr xs
                      in nest 2 $ fsep $ punctuate comma (mkOr ss)
                    ]
      format (render doc) "*Intro*"
    Info_Version -> format ("Agda version " ++ versionWithCommitInfo) "*Agda Version*"
    Info_GoalSpecific ii kind -> lispifyGoalSpecificDisplayInfo ii kind

lispifyGoalSpecificDisplayInfo :: InteractionId -> GoalDisplayInfo -> TCM [Lisp String]
lispifyGoalSpecificDisplayInfo ii kind = localTCState $ B.withInteractionId ii $
  case kind of
    Goal_HelperFunction helperType -> do
      doc <- inTopContext $ prettyATop helperType
      return [ L [ A "agda2-info-action-and-copy"
                 , A $ quote "*Helper function*"
                 , A $ quote (render doc ++ "\n")
                 , A "nil"
                 ]
             ]
    Goal_NormalForm cmode expr -> do
      doc <- showComputed cmode expr
      format (render doc) "*Normal Form*"   -- show?
    Goal_GoalType norm aux ctx constraints -> do
      ctxDoc <- prettyResponseContext ii True ctx
      goalDoc <- prettyTypeOfMeta norm ii
      auxDoc <- case aux of
            GoalOnly -> return empty
            GoalAndHave expr -> do
              doc <- prettyATop expr
              return $ "Have:" <+> doc
            GoalAndElaboration term -> do
              doc <- TCP.prettyTCM term
              return $ "Elaborates to:" <+> doc
      let constraintsDoc = if (null constraints)
            then  []
            else  [ text $ delimiter "Constraints"
                  , vcat $ map pretty constraints
                  ]
      let doc = vcat $
            [ "Goal:" <+> goalDoc
            , auxDoc
            , text (replicate 60 '\x2014')
            , ctxDoc
            ] ++ constraintsDoc
      format (render doc) "*Goal type etc.*"
    Goal_CurrentGoal norm -> do
      doc <- prettyTypeOfMeta norm ii
      format (render doc) "*Current Goal*"
    Goal_InferredType expr -> do
      doc <- prettyATop expr
      format (render doc) "*Inferred Type*"

-- | Format responses of DisplayInfo

format :: String -> String -> TCM [Lisp String]
format content bufname = return [ display_info' False bufname content ]

-- | Adds a \"last\" tag to a response.

lastTag :: Integer -> Lisp String -> Lisp String
lastTag n r = Cons (Cons (A "last") (A $ show n)) r

-- | Show an iteraction point identifier as an elisp expression.

showNumIId :: InteractionId -> Lisp String
showNumIId = A . show . interactionId

--------------------------------------------------------------------------------

-- | Given strings of goals, warnings and errors, return a pair of the
--   body and the title for the info buffer
formatWarningsAndErrors :: String -> String -> String -> (String, String)
formatWarningsAndErrors g w e = (body, title)
  where
    isG = not $ null g
    isW = not $ null w
    isE = not $ null e
    title = List.intercalate "," $ catMaybes
              [ " Goals"    <$ guard isG
              , " Errors"   <$ guard isE
              , " Warnings" <$ guard isW
              , " Done"     <$ guard (not (isG || isW || isE))
              ]

    body = List.intercalate "\n" $ catMaybes
             [ g                    <$ guard isG
             , delimiter "Errors"   <$ guard (isE && (isG || isW))
             , e                    <$ guard isE
             , delimiter "Warnings" <$ guard (isW && (isG || isE))
             , w                    <$ guard isW
             ]


-- | Serializing Info_Error
showInfoError :: Info_Error -> TCM String
showInfoError (Info_GenericError err) = do
  e <- prettyError err
  w <- prettyTCWarnings' =<< getAllWarningsOfTCErr err

  let errorMsg  = if null w
                      then e
                      else delimiter "Error" ++ "\n" ++ e
  let warningMsg = List.intercalate "\n" $ delimiter "Warning(s)"
                                      : filter (not . null) w
  return $ if null w
            then errorMsg
            else errorMsg ++ "\n\n" ++ warningMsg
showInfoError (Info_CompilationError warnings) = do
  s <- prettyTCWarnings warnings
  return $ unlines
            [ "You need to fix the following errors before you can compile"
            , "the module:"
            , ""
            , s
            ]
showInfoError (Info_HighlightingParseError ii) =
  return $ "Highlighting failed to parse expression in " ++ show ii
showInfoError (Info_HighlightingScopeCheckError ii) =
  return $ "Highlighting failed to scope check expression in " ++ show ii

explainWhyInScope :: FilePath
                  -> String
                  -> (Maybe LocalVar)
                  -> [AbstractName]
                  -> [AbstractModule]
                  -> TCM Doc
explainWhyInScope s _ Nothing [] [] = TCP.text (s ++ " is not in scope.")
explainWhyInScope s _ v xs ms = TCP.vcat
  [ TCP.text (s ++ " is in scope as")
  , TCP.nest 2 $ TCP.vcat [variable v xs, modules ms]
  ]
  where
    -- variable :: Maybe _ -> [_] -> TCM Doc
    variable Nothing vs = names vs
    variable (Just x) vs
      | null vs   = asVar
      | otherwise = TCP.vcat
         [ TCP.sep [ asVar, TCP.nest 2 $ shadowing x]
         , TCP.nest 2 $ names vs
         ]
      where
        asVar :: TCM Doc
        asVar = do
          "* a variable bound at" TCP.<+> TCP.prettyTCM (nameBindingSite $ localVar x)
        shadowing :: LocalVar -> TCM Doc
        shadowing (LocalVar _ _ [])    = "shadowing"
        shadowing _ = "in conflict with"
    names   = TCP.vcat . map pName
    modules = TCP.vcat . map pMod

    pKind = \case
      ConName                  -> "constructor"
      FldName                  -> "record field"
      PatternSynName           -> "pattern synonym"
      GeneralizeName           -> "generalizable variable"
      DisallowedGeneralizeName -> "generalizable variable from let open"
      MacroName                -> "macro name"
      QuotableName             -> "quotable name"
      -- previously DefName:
      DataName                 -> "data type"
      RecName                  -> "record type"
      AxiomName                -> "postulate"
      PrimName                 -> "primitive function"
      FunName                  -> "defined name"
      OtherDefName             -> "defined name"

    pName :: AbstractName -> TCM Doc
    pName a = TCP.sep
      [ "* a"
        TCP.<+> pKind (anameKind a)
        TCP.<+> TCP.text (prettyShow $ anameName a)
      , TCP.nest 2 $ "brought into scope by"
      ] TCP.$$
      TCP.nest 2 (pWhy (nameBindingSite $ qnameName $ anameName a) (anameLineage a))
    pMod :: AbstractModule -> TCM Doc
    pMod  a = TCP.sep
      [ "* a module" TCP.<+> TCP.text (prettyShow $ amodName a)
      , TCP.nest 2 $ "brought into scope by"
      ] TCP.$$
      TCP.nest 2 (pWhy (nameBindingSite $ qnameName $ mnameToQName $ amodName a) (amodLineage a))

    pWhy :: Range -> WhyInScope -> TCM Doc
    pWhy r Defined = "- its definition at" TCP.<+> TCP.prettyTCM r
    pWhy r (Opened (C.QName x) w) | isNoName x = pWhy r w
    pWhy r (Opened m w) =
      "- the opening of"
      TCP.<+> TCP.prettyTCM m
      TCP.<+> "at"
      TCP.<+> TCP.prettyTCM (getRange m)
      TCP.$$
      pWhy r w
    pWhy r (Applied m w) =
      "- the application of"
      TCP.<+> TCP.prettyTCM m
      TCP.<+> "at"
      TCP.<+> TCP.prettyTCM (getRange m)
      TCP.$$
      pWhy r w


-- | Pretty-prints the context of the given meta-variable.

prettyResponseContext
  :: InteractionId  -- ^ Context of this meta-variable.
  -> Bool           -- ^ Print the elements in reverse order?
  -> [ResponseContextEntry]
  -> TCM Doc
prettyResponseContext ii rev ctx = withInteractionId ii $ do
  mod   <- asksTC getModality
  align 10 . applyWhen rev reverse <$> do
    forM ctx $ \ (ResponseContextEntry n x (Arg ai expr) nis) -> do
      let
        prettyCtxName :: String
        prettyCtxName
          | n == x                 = prettyShow x
          | isInScope n == InScope = prettyShow n ++ " = " ++ prettyShow x
          | otherwise              = prettyShow x

        -- Some attributes are useful to report whenever they are not
        -- in the default state.
        attribute :: String
        attribute = c ++ if null c then "" else " "
          where c = prettyShow (getCohesion ai)

        extras :: [Doc]
        extras = concat $
          [ [ "not in scope" | isInScope nis == C.NotInScope ]
            -- Print erased if hypothesis is erased by goal is non-erased.
          , [ "erased"       | not $ getQuantity  ai `moreQuantity` getQuantity  mod ]
            -- Print irrelevant if hypothesis is strictly less relevant than goal.
          , [ "irrelevant"   | not $ getRelevance ai `moreRelevant` getRelevance mod ]
          ]
      doc <- prettyATop expr
      return (attribute ++ prettyCtxName, ":" <+> (doc <> parenSep extras))
  where
    parenSep :: [Doc] -> Doc
    parenSep docs
      | null docs = empty
      | otherwise = (" " <+>) $ parens $ fsep $ punctuate comma docs


-- | Print open metas nicely.
showGoals :: Goals -> TCM String
showGoals (ims, hms) = do
  di <- forM ims $ \ i ->
    B.withInteractionId (B.outputFormId $ B.OutputForm noRange [] i) $
      prettyATop i
  dh <- mapM showA' hms
  return $ unlines $ map show di ++ dh
  where
    metaId (B.OfType i _) = i
    metaId (B.JustType i) = i
    metaId (B.JustSort i) = i
    metaId (B.Assign i _) = i
    metaId _ = __IMPOSSIBLE__
    showA' :: B.OutputConstraint A.Expr NamedMeta -> TCM String
    showA' m = do
      let i = nmid $ metaId m
      r <- getMetaRange i
      d <- B.withMetaId i (prettyATop m)
      return $ show d ++ "  [ at " ++ show r ++ " ]"

-- | Pretty-prints the type of the meta-variable.

prettyTypeOfMeta :: B.Rewrite -> InteractionId -> TCM Doc
prettyTypeOfMeta norm ii = do
  form <- B.typeOfMeta norm ii
  case form of
    B.OfType _ e -> prettyATop e
    _            -> prettyATop form


-- | Prefix prettified CPUTime with "Time:"
prettyTimed :: CPUTime -> Doc
prettyTimed time = "Time:" <+> pretty time
