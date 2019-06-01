
module Agda.Interaction.EmacsTop
    ( mimicGHCi
    ) where

import Control.Monad.State
import qualified Data.List as List
import System.FilePath

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
import Agda.Interaction.AgdaTop
import Agda.Interaction.BasicOps as B
import Agda.Interaction.Response as R
import Agda.Interaction.EmacsCommand hiding (putResponse)
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Precise (TokenBased(..))
import Agda.Interaction.InteractionTop (showGoals, prettyTimed, localStateCommandM)
import Agda.Interaction.Imports (getAllWarningsOfTCErr)

import Agda.Utils.FileName (filePath)
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Null (empty)
import Agda.Utils.Maybe
import Agda.Utils.Pretty
import Agda.Utils.String
import Agda.VersionCommit

----------------------------------

-- | 'mimicGHCi' is a fake ghci interpreter for the Emacs frontend
--   and for interaction tests.
--
--   'mimicGHCi' reads the Emacs frontend commands from stdin,
--   interprets them and print the result into stdout.
mimicGHCi :: TCM () -> TCM ()
mimicGHCi = repl (liftIO . mapM_ print <=< lispifyResponse) "Agda2> "

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

-- | Convert Response to an elisp value for the interactive emacs frontend.

lispifyResponse :: Response -> TCM [Lisp String]
lispifyResponse (Resp_HighlightingInfo info remove method modFile) =
  (:[]) <$> liftIO (lispifyHighlightingInfo info remove method modFile)
lispifyResponse (Resp_DisplayInfo info) = case info of
    Info_CompilationOk (w, e) -> do
      warnings <- prettyTCWarnings w
      errors <- prettyTCWarnings e
      -- abusing the goals field since we ignore the title
      let (body, _) = formatWarningsAndErrors
                        "The module was successfully compiled.\n"
                        warnings
                        errors
      f body "*Compilation result*"
    Info_Constraints s -> f (show $ vcat $ map pretty s) "*Constraints*"
    Info_AllGoalsWarnings ms (w, e) -> do
      goals <- showGoals ms
      warnings <- prettyTCWarnings w
      errors <- prettyTCWarnings e
      let (body, title) = formatWarningsAndErrors goals warnings errors
      f body ("*All" ++ title ++ "*")
    Info_Auto s -> f s "*Auto*"
    Info_Error err -> do
      s <- serializeInfoError err
      f s "*Error*"
    Info_Time s -> f (render $ prettyTimed s) "*Time*"
    Info_NormalForm_TopLevel state cmode time expr -> do
      doc <- evalStateT prettyExpr state
      f (render $ maybe empty prettyTimed time $$ doc) "*Normal Form*"
      where
        prettyExpr = localStateCommandM
            $ lift
            $ B.atTopLevel
            $ allowNonTerminatingReductions
            $ (if computeIgnoreAbstract cmode then ignoreAbstractMode else inConcreteMode)
            $ (B.showComputed cmode)
            $ expr
    Info_NormalForm cmode ii expr -> do
      doc <- localTCState $ B.withInteractionId ii $ showComputed cmode expr
      f (render doc) "*Normal Form*"   -- show?
    Info_InferredType_TopLevel state time expr -> do
      doc <- evalStateT prettyExpr state
      f (render $ maybe empty prettyTimed time $$ doc) "*Inferred Type*"
      where
        prettyExpr = localStateCommandM
            $ lift
            $ B.atTopLevel
            $ TCP.prettyA
            $ expr
    -- f (render s) "*Inferred Type*"
    Info_InferredType ii expr -> do
      doc <- localTCState $ B.withInteractionId ii $ prettyATop expr
      f (render doc) "*Inferred Type*"
    Info_CurrentGoal s -> f (render s) "*Current Goal*"
    Info_GoalType s -> f (render s) "*Goal type etc.*"
    Info_ModuleContents modules tel types -> do
      s <- localTCState $ do
        types' <- addContext tel $ forM types $ \ (x, t) -> do
          t <- prettyTCM t
          return (prettyShow x, ":" <+> t)
        return $ vcat
          [ "Modules"
          , nest 2 $ vcat $ map pretty modules
          , "Names"
          , nest 2 $ align 10 types'
          ]
      f (render s) "*Module contents*"
    Info_SearchAbout hits names -> do
      fancy <- forM hits $ \ (x, t) -> do
        t <- prettyTCM t
        return (prettyShow x, ":" <+> t)
      let s = "Definitions about" <+> text (List.intercalate ", " $ words names) $$
                nest 2 (align 10 fancy)
      f (render s) "*Search About*"
    Info_WhyInScope s cwd v xs ms -> do
      result <- explainWhyInScope s cwd v xs ms
      f (render result) "*Scope Info*"
    Info_Context ctx -> do
      doc <- localTCState (prettyRespContext False ctx)
      f (render doc) "*Context*"
    Info_HelperFunction s -> return [ L [ A "agda2-info-action-and-copy"
                                 , A $ quote "*Helper function*"
                                 , A $ quote (render s ++ "\n")
                                 , A "nil"
                                 ]
                             ]
    Info_Intro_NotFound -> f "No introduction forms found." "*Intro*"
    Info_Intro_ConstructorUnknown ss -> do
      let msg = sep [ "Don't know which constructor to introduce of"
                    , let mkOr []     = []
                          mkOr [x, y] = [text x <+> "or" <+> text y]
                          mkOr (x:xs) = text x : mkOr xs
                      in nest 2 $ fsep $ punctuate comma (mkOr ss)
                    ]
      f (render $ pretty msg) "*Intro*"
    Info_Version -> f ("Agda version " ++ versionWithCommitInfo) "*Agda Version*"
  where f content bufname = return [ display_info' False bufname content ]
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

-- | Adds a \"last\" tag to a response.

lastTag :: Integer -> Lisp String -> Lisp String
lastTag n r = Cons (Cons (A "last") (A $ show n)) r

-- | Show an iteraction point identifier as an elisp expression.

showNumIId :: InteractionId -> Lisp String
showNumIId = A . show . interactionId

--------------------------------------------------------------------------------

-- | Serializing Info_Error
serializeInfoError :: Info_Error -> TCM String
serializeInfoError (Info_GenericError err) = do
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
serializeInfoError (Info_CompilationError warnings) = do
  s <- prettyTCWarnings warnings
  return $ unlines
            [ "You need to fix the following errors before you can compile"
            , "the module:"
            , ""
            , s
            ]
serializeInfoError (Info_HighlightingParseError ii) =
  return $ "Highlighting failed to parse expression in " ++ show ii
serializeInfoError (Info_HighlightingScopeCheckError ii) =
  return $ "Highlighting failed to scope check expression in " ++ show ii

explainWhyInScope :: FilePath
                  -> String
                  -> (Maybe LocalVar)
                  -> [AbstractName]
                  -> [AbstractModule]
                  -> TCM Doc
explainWhyInScope s _ Nothing [] [] = TCP.text (s ++ " is not in scope.")
explainWhyInScope s cwd v xs ms = TCP.vcat
  [ TCP.text (s ++ " is in scope as")
  , TCP.nest 2 $ TCP.vcat [variable v xs, modules ms]
  ]
  where
    prettyRange :: Range -> TCM Doc
    prettyRange r = pretty . (fmap . fmap) mkRel <$> do
      return r
    mkRel = makeRelative cwd . filePath

    -- variable :: Maybe _ -> [_] -> TCM Doc
    variable Nothing xs = names xs
    variable (Just x) xs
      | null xs   = asVar
      | otherwise = TCP.vcat
         [ TCP.sep [ asVar, TCP.nest 2 $ shadowing x]
         , TCP.nest 2 $ names xs
         ]
      where
        asVar :: TCM Doc
        asVar = do
          "* a variable bound at" TCP.<+> TCP.prettyTCM (nameBindingSite $ localVar x)
        shadowing :: LocalVar -> TCM Doc
        shadowing (LocalVar _ _ [])    = "shadowing"
        shadowing _ = "in conflict with"
    names   xs = TCP.vcat $ map pName xs
    modules ms = TCP.vcat $ map pMod ms

    pKind DefName        = "defined name"
    pKind ConName        = "constructor"
    pKind FldName        = "record field"
    pKind PatternSynName = "pattern synonym"
    pKind GeneralizeName = "generalizable variable"
    pKind DisallowedGeneralizeName = "generalizable variable from let open"
    pKind MacroName      = "macro name"
    pKind QuotableName   = "quotable name"

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

prettyRespContext
  :: Bool           -- ^ Print the elements in reverse order?
  -> [RespContextEntry]
  -> TCM Doc
prettyRespContext rev ctx = do
  pairs <- mapM compose ctx
  return $ align 10 $ applyWhen rev reverse pairs
  where
    compose :: RespContextEntry -> TCM (String, Doc)
    compose (a, b, c, d) = do
      t <- prettyCtxType c d
      return (prettyCtxName a b, t)
    prettyCtxName :: C.Name -> C.Name -> String
    prettyCtxName n x
      | n == x                 = prettyShow x
      | isInScope n == InScope = prettyShow n ++ " = " ++ prettyShow x
      | otherwise              = prettyShow x
    prettyCtxType :: A.Expr -> NameInScope -> TCM Doc
    prettyCtxType expr nis = do
      doc <- prettyATop expr
      return $ ":" <+> (doc <> notInScopeMarker nis)
    notInScopeMarker :: NameInScope -> Doc
    notInScopeMarker nis = case isInScope nis of
      C.InScope    -> ""
      C.NotInScope -> "  (not in scope)"
