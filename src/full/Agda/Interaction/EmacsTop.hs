
module Agda.Interaction.EmacsTop
    ( mimicGHCi
    ) where

import Control.Monad.State
import qualified Data.List as List

import Agda.Utils.Maybe
import Agda.Utils.Pretty
import Agda.Utils.String

import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty.Warning (prettyTCWarnings, prettyTCWarnings')
import Agda.TypeChecking.Errors (prettyError)

import Agda.Interaction.AgdaTop
import Agda.Interaction.Response as R
import Agda.Interaction.EmacsCommand hiding (putResponse)
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Precise (TokenBased(..))
import Agda.Interaction.InteractionTop (showGoals, prettyTimed)
import Agda.Interaction.Imports (getAllWarningsOfTCErr)
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
    Info_NormalForm s -> f (render s) "*Normal Form*"   -- show?
    Info_InferredType s -> f (render s) "*Inferred Type*"
    Info_CurrentGoal s -> f (render s) "*Current Goal*"
    Info_GoalType s -> f (render s) "*Goal type etc.*"
    Info_ModuleContents s -> f (render s) "*Module contents*"
    Info_SearchAbout s -> f (render s) "*Search About*"
    Info_WhyInScope s -> f (render s) "*Scope Info*"
    Info_Context s -> f (render s) "*Context*"
    Info_HelperFunction s -> return [ L [ A "agda2-info-action-and-copy"
                                 , A $ quote "*Helper function*"
                                 , A $ quote (render s ++ "\n")
                                 , A "nil"
                                 ]
                             ]
    Info_Intro s -> f (render $ pretty s) "*Intro*"
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

instance Pretty Info_Intro where
  pretty (Info_Intro_NotFound) = "No introduction forms found."
  pretty (Info_Intro_ConstructorUnknown ss) =
    sep [ "Don't know which constructor to introduce of"
        , let mkOr []     = []
              mkOr [x, y] = [text x <+> "or" <+> text y]
              mkOr (x:xs) = text x : mkOr xs
          in nest 2 $ fsep $ punctuate comma (mkOr ss)
        ]
