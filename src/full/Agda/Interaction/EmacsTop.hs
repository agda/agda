{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.EmacsTop
    ( mimicGHCi
    , namedMetaOf
    , showInfoError
    , prettyGoals
    , prettyInfoError
    , explainWhyInScope
    , prettyResponseContext
    , prettyTypeOfMeta
    ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.State    ( evalStateT )
import Control.Monad.Trans    ( lift )

import Data.List qualified as List
import Data.Text qualified as Text

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Abstract.Pretty (prettyATop)
import Agda.Syntax.Concrete as C

import Agda.TypeChecking.Errors ( tcErrModuleToSource, explainWhyInScope, getAllWarningsOfTCErr, verbalize, prettyError )
import Agda.TypeChecking.Pretty qualified as TCP
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Pretty.Warning (prettyTCWarnings')
import Agda.TypeChecking.Monad

import Agda.Interaction.AgdaTop
import Agda.Interaction.Base
import Agda.Interaction.BasicOps as B
import Agda.Interaction.Response as R
import Agda.Interaction.Emacs.Lisp
import Agda.Interaction.EmacsCommand ( displayInfo, clearRunningInfo, displayRunningInfo)
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Precise (TokenBased(..))
import Agda.Interaction.Command (localStateCommandM)
import Agda.Interaction.Options ( DiagnosticsColours(..), optDiagnosticsColour )

import Agda.Utils.DocTree  ( treeToTextNoAnn, renderToTree )
import Agda.Utils.Function ( applyWhen )
import Agda.Utils.Functor  ( (<.>) )
import Agda.Utils.Lens
import Agda.Utils.Null
import Agda.Utils.Maybe
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
mimicGHCi = repl (liftIO . putStrLn . prettyShow <=< lispifyResponse) "Agda2> "

-- | Convert Response to an elisp value for the interactive emacs frontend.

lispifyResponse :: Response -> TCM (Lisp String)
lispifyResponse = \case

  Resp_HighlightingInfo info remove method modFile ->
    liftIO (lispifyHighlightingInfo info remove method modFile)

  Resp_DisplayInfo info ->
    lispifyDisplayInfo info

  Resp_ClearHighlighting tokenBased ->
    return $ L $
      A "agda2-highlight-clear" :
      case tokenBased of
        TokenBased -> [ Q (lispifyTokenBased tokenBased) ]
        NotOnlyTokenBased -> []

  Resp_DoneAborting ->
    return $ L [ A "agda2-abort-done" ]

  Resp_DoneExiting ->
    return $ L [ A "agda2-exit-done" ]

  Resp_ClearRunningInfo ->
    return clearRunningInfo

  Resp_RunningInfo n docTree
    | n <= 1 -> do
        displayRunningInfo docTree <$> wantBufferHighlighting Nothing
    | otherwise ->
        return $ L [ A "agda2-verbose", A (quote $ Text.unpack $ treeToTextNoAnn docTree) ]
        -- TODO: do we want colored debug-printout?

  Resp_Status s ->
    return $ L
      [ A "agda2-status-action"
      , A (quote $ List.intercalate "," $ catMaybes [checked, showImpl, showIrr])
      ]
    where
      checked  = boolToMaybe (sChecked                 s) "Checked"
      showImpl = boolToMaybe (sShowImplicitArguments   s) "ShowImplicit"
      showIrr  = boolToMaybe (sShowIrrelevantArguments s) "ShowIrrelevant"

  Resp_JumpToError f p ->
    return $ lastTag 3 $ L
      [ A "agda2-maybe-goto"
      , Q $ L [ A (quote f), A ".", A (show p) ]
      ]

  Resp_InteractionPoints is ->
    return $ lastTag 1 $ L
      [ A "agda2-goals-action"
      , Q $ L $ map showNumIId is
      ]

  Resp_GiveAction ii s ->
    return $ L
      [ A "agda2-give-action"
      , showNumIId ii
      , A s'
      ]
    where
      s' = case s of
          Give_String str -> quote str
          Give_Paren      -> "'paren"
          Give_NoParen    -> "'no-paren"

  Resp_MakeCase ii variant pcs ->
    return $ lastTag 2 $ L
      [ A cmd
      , Q $ L $ map (A . quote) pcs
      ]
    where
    cmd = case variant of
      R.Function       -> "agda2-make-case-action"
      R.ExtendedLambda -> "agda2-make-case-action-extendlam"

  Resp_SolveAll ps ->
    return $ lastTag 2 $ L
      [ A "agda2-solveAll-action"
      , Q $ L $ concatMap prn ps
      ]
    where
      prn (ii,e)= [showNumIId ii, A $ quote $ prettyShow e]

  Resp_Mimer ii msol ->
    return $ lastTag 1 $ L $ case msol of
      Nothing ->
        [ A "agda2-info-action"
        , A $ quote "*Mimer*"
        , A $ quote "No solution found"
        ]
      Just str ->
        [ A "agda2-solve-action"
        , showNumIId ii
        , A $ quote str
        ]

lispifyDisplayInfo :: DisplayInfo -> TCM (Lisp String)
lispifyDisplayInfo = \case

    Info_CompilationOk backend ws -> do
      warnings <- prettyTCWarnings' (tcWarnings ws)
      errors   <- prettyTCWarnings' (nonFatalErrors ws)
      let
        msg = hcat
          [ "The module was successfully compiled with backend "
          , pretty backend
          , ".\n"
          ]
      -- abusing the goals field since we ignore the title
        (_title, body) = formatWarningsAndErrors msg warnings errors
      format "*Compilation result*" body

    Info_Constraints s -> do
      doc <- TCP.vcat $ map prettyTCM s
      format "*Constraints*" doc

    Info_AllGoalsWarnings ms ws -> do
      goals    <- prettyGoals ms
      warnings <- prettyTCWarnings' (tcWarnings ws)
      errors   <- prettyTCWarnings' (nonFatalErrors ws)
      let (title, body) = formatWarningsAndErrors goals warnings errors
      format ("*All" ++ title ++ "*") body

    Info_Auto s ->
      format "*Auto*" $ P.text s

    Info_Error err -> do
      uncurry (format' "*Error*") =<< prettyInfoError err

    Info_Time time ->
      format "*Time*" $ prettyTimed time

    Info_NormalForm state cmode time expr -> do
      exprDoc <- evalStateT prettyExpr state
      let doc = maybe empty prettyTimed time $$ exprDoc
          lbl | cmode == HeadCompute = "*Head Normal Form*"
              | otherwise            = "*Normal Form*"
      format lbl doc
      where
        prettyExpr = localStateCommandM
            $ lift
            $ B.atTopLevel
            $ (B.withComputeIgnoreAbstract cmode)
            $ (B.showComputed cmode)
            $ expr

    Info_InferredType state time expr -> do
      exprDoc <- evalStateT prettyExpr state
      let doc = maybe empty prettyTimed time $$ exprDoc
      format "*Inferred Type*" doc
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
      format "*Module contents*" doc

    Info_SearchAbout hits names -> do
      hitDocs <- forM hits $ \ (x, t) -> do
        doc <- prettyTCM t
        return (prettyShow x, ":" <+> doc)
      let doc = "Definitions about" <+>
                text (List.intercalate ", " $ words names) $$ nest 2 (align 10 hitDocs)
      format "*Search About*" doc

    Info_WhyInScope why -> do
      doc <- explainWhyInScope why
      format "*Scope Info*" doc

    Info_Context ii ctx -> do
      doc <- localTCState (prettyResponseContext ii False ctx)
      format "*Context*" doc

    Info_Intro_NotFound ->
      format "*Intro*" "No introduction forms found."

    Info_Intro_ConstructorUnknown ss -> do
      let doc = sep [ "Don't know which constructor to introduce of"
                    , let mkOr []     = []
                          mkOr [x, y] = [text x <+> "or" <+> text y]
                          mkOr (x:xs) = text x : mkOr xs
                      in nest 2 $ fsep $ punctuate comma (mkOr ss)
                    ]
      format "*Intro*" doc

    Info_Version ->
      format "*Agda Version*" ("Agda version" <+> text versionWithCommitInfo)

    Info_GoalSpecific ii kind ->
      lispifyGoalSpecificDisplayInfo ii kind

lispifyGoalSpecificDisplayInfo :: InteractionId -> GoalDisplayInfo -> TCM (Lisp String)
lispifyGoalSpecificDisplayInfo ii kind = localTCState $ withInteractionId ii $
  case kind of

    Goal_HelperFunction helperType -> do
      doc <- inTopContext $ prettyATop helperType
      return $ L
        [ A "agda2-info-action-and-copy"
        , A $ quote "*Helper function*"
        , A $ quote (render doc ++ "\n")
        , A "nil"
        ]

    Goal_NormalForm cmode expr -> do
      doc <- showComputed cmode expr
      format "*Normal Form*" doc

    Goal_GoalType norm aux ctx bndry constraints -> do
      ctxDoc <- prettyResponseContext ii True ctx
      goalDoc <- prettyTypeOfMeta norm ii
      let boundaryDoc hd bndry
            | null bndry = []
            | otherwise  = [ text $ delimiter hd
                           , vcat $ map pretty bndry
                           ]
      auxDoc <- case aux of
            GoalOnly -> return empty
            GoalAndHave expr bndry -> do
              doc <- prettyATop expr
              return $ ("Have:" <+> doc) $$ vcat (boundaryDoc ("Boundary (actual)") bndry)
            GoalAndElaboration expr -> do
              doc <- prettyATop expr
              return $ "Elaborates to:" <+> doc
      let constraintsDoc
            | null constraints = []
            | otherwise        =
              [ TCP.text $ delimiter "Constraints"
              , TCP.vcat $ map prettyTCM constraints
              ]
      doc <- TCP.vcat $ concat
        [ [ "Goal:" TCP.<+> return goalDoc
          , return (vcat (boundaryDoc "Boundary (wanted)" bndry))
          , return auxDoc
          ]
        , [ TCP.text (delimiter "Context") | not $ null ctxDoc ]
        , [ return ctxDoc ]
        , constraintsDoc
        ]
      format "*Goal type etc.*" doc

    Goal_CurrentGoal norm -> do
      doc <- prettyTypeOfMeta norm ii
      format "*Current Goal*" doc

    Goal_InferredType expr -> do
      doc <- prettyATop expr
      format "*Inferred Type*" doc

format :: String -> Doc -> TCM (Lisp String)
format header = format' header Nothing

-- | Format responses of 'DisplayInfo'.
format'
  :: String
  -- ^ String to use as a header.
  -> Maybe ModuleToSource
  -- ^ Map of module names to source files *as used in the context of the 'Doc'*.
  --
  -- Note: 'Nothing' does not mean "do not highlight", it means "use the
  -- current 'ModuleToSource'". This is appropriate if the 'Doc' was
  -- generated in a TC state which the current state descends from, but
  -- not if it was generated in a now-discarded state (e.g.: an error in
  -- an imported module).
  -> Doc
  -- ^ The document to print.
  -> TCM (Lisp String)
format' header m2s content = displayInfo header (renderToTree content) False <$>
  wantBufferHighlighting m2s

-- | Do we want highlighting in the Agda information buffer?
--   'Nothing' with option @--color=never@.
wantBufferHighlighting
  :: Maybe ModuleToSource
  -- ^ If 'Just', use the given 'ModuleToSource' instead of the one from
  -- the TC state.
  -> TCM (Maybe ModuleToSource)
wantBufferHighlighting other = do
  col <- commandLineOptions <&> optDiagnosticsColour <&> \case
    AutoColour   -> True
    AlwaysColour -> True
    NeverColour  -> False
  if col
    then Just <$> maybe (useTC stModuleToSource) pure other
    else return Nothing

-- | Adds a \"last\" tag to a response.

lastTag :: Integer -> Lisp String -> Lisp String
lastTag n r = Cons (Cons (A "last") (A $ show n)) r

-- | Show an iteraction point identifier as an elisp expression.

showNumIId :: InteractionId -> Lisp String
showNumIId = A . show . interactionId

--------------------------------------------------------------------------------

-- | Given goals, warnings and errors, return a pair of the
--   title and the body for the info buffer.
formatWarningsAndErrors :: Doc -> [Doc] -> [Doc] -> (String, Doc)
formatWarningsAndErrors g ws es = (title, body)
  where
    isG = not $ null g
    isW = not $ null ws
    isE = not $ null es
    title = List.intercalate "," $ concat
      [ [ " Goals"    | isG ]
      , [ " Errors"   | isE ]
      , [ " Warnings" | isW ]
      , [ " Done"     | not (isG || isW || isE) ]
      ]
    body = vcat $ concat
      [ [ g ]
      , [ text $ delimiter "Error"    | isE && (isG || isW) ]
      , es
      , [ text $ delimiter "Warnings" | isW && (isG || isE) ]
      , ws
      ]

-- | Serializing 'Info_Error'.
showInfoError :: Info_Error -> TCM String
showInfoError = (render . snd) <.> prettyInfoError

-- | Turn an 'Info_Error' into a 'Doc'. Possibly returns a
-- 'ModuleToSource' appropriate for rendering the returned 'Doc'.
--
-- A 'Nothing' return only indicates that the 'Doc' can be safely
-- rendered in the current TC state. Pass this value to
-- 'wantBufferHighlighting' to respect whether the user wants syntax
-- colouring.
prettyInfoError :: Info_Error -> TCM (Maybe ModuleToSource, Doc)
prettyInfoError = \case
  Info_GenericError err -> do
    e  <- prettyError err
    ws <- prettyTCWarnings' =<< getAllWarningsOfTCErr err
    let (_title, body) = formatWarningsAndErrors empty ws [e]
    return (tcErrModuleToSource err, body)

  Info_CompilationError warnings -> do
    docs <- prettyTCWarnings' warnings
    return . (Nothing,) $ vcat $
      "You need to fix the following errors before you can compile the module:" :
      "" :
      docs

  Info_HighlightingParseError ii ->
    return . (Nothing,) $ "Highlighting failed to parse expression in" <+> pretty ii

  Info_HighlightingScopeCheckError ii ->
    return . (Nothing,) $ "Highlighting failed to scope check expression in" <+> pretty ii

-- | Pretty-prints the context of the given meta-variable.

prettyResponseContext
  :: InteractionId  -- ^ Context of this meta-variable.
  -> Bool           -- ^ Print the elements in reverse order?
  -> [ResponseContextEntry]
  -> TCM Doc
prettyResponseContext ii rev ctx = withInteractionId ii $ do
  mod <- currentModality
  align 10 . concat . applyWhen rev reverse <$> do
    forM ctx $ \ (ResponseContextEntry n x (Arg ai expr) letv nis) -> do
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

        pol :: ModalPolarity
        pol = modPolarityAnn $ getModalPolarity ai

        extras :: [Doc]
        extras = concat $
          [ [ "not in scope" | isInScope nis == C.NotInScope ]
            -- Print "erased" if hypothesis is erased but goal is non-erased.
          , [ "erased"       | not $ getQuantity  ai `moreQuantity` getQuantity  mod ]
            -- Print relevance of hypothesis relative to relevance of the goal. (Issue #6706.)
          , [ text $ verbalize r
                             | let r = getRelevance mod `inverseComposeRelevance` getRelevance ai
                             , not $ isRelevant r ]
          , [ text $ verbalize pol | not $ pol == MixedPolarity ]
            -- Print "instance" if variable is considered by instance search.
          , [ "instance"     | isInstance ai ]
          ]
      ty <- prettyATop expr
      maybeVal <- traverse prettyATop letv

      return $
        (attribute ++ prettyCtxName, ":" <+> ty <+> (parenSep extras)) :
        [ (prettyShow x, "=" <+> val) | val <- maybeToList maybeVal ]

  where
    parenSep :: [Doc] -> Doc
    parenSep docs
      | null docs = empty
      | otherwise = (" " <+>) $ parens $ fsep $ punctuate comma docs


-- | Pretty-prints the type of the meta-variable.

prettyTypeOfMeta :: Rewrite -> InteractionId -> TCM Doc
prettyTypeOfMeta norm ii = do
  B.typeOfMeta norm ii >>= \case
    OfType _ e -> prettyATop e
    form       -> prettyATop form

-- | Prefix prettified CPUTime with "Time:"
prettyTimed :: CPUTime -> Doc
prettyTimed time = "Time:" <+> pretty time
