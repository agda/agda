-- {-# LANGUAGE CPP #-}

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

import Agda.Interaction.AgdaTop
import Agda.Interaction.Response as R
import Agda.Interaction.EmacsCommand hiding (putResponse)
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Precise (TokenBased(..))

import Agda.VersionCommit

----------------------------------

-- | 'mimicGHCi' is a fake ghci interpreter for the Emacs frontend
--   and for interaction tests.
--
--   'mimicGHCi' reads the Emacs frontend commands from stdin,
--   interprets them and print the result into stdout.
mimicGHCi :: TCM () -> TCM ()
mimicGHCi = repl (liftIO . mapM_ print <=< liftIO . lispifyResponse) "Agda2> "

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
              , " Warnings" <$ guard isW
              , " Errors"   <$ guard isE
              , " Done"     <$ guard (not (isG || isW || isE))
              ]

    body = List.intercalate "\n" $ catMaybes
             [ g                    <$ guard isG
             , delimiter "Warnings" <$ guard (isW && (isG || isE))
             , w                    <$ guard isW
             , delimiter "Errors"   <$ guard (isE && (isG || isW))
             , e                    <$ guard isE
             ]

-- | Convert Response to an elisp value for the interactive emacs frontend.

lispifyResponse :: Response -> IO [Lisp String]
lispifyResponse (Resp_HighlightingInfo info remove method modFile) =
  (:[]) <$> lispifyHighlightingInfo info remove method modFile
lispifyResponse (Resp_DisplayInfo info) = return $ case info of
    Info_CompilationOk w e -> f body "*Compilation result*"
      where (body, _) = formatWarningsAndErrors "The module was successfully compiled.\n" w e -- abusing the goals field since we ignore the title
    Info_Constraints s -> f s "*Constraints*"
    Info_AllGoalsWarnings _ g w e -> f body ("*All" ++ title ++ "*")
      where (body, title) = formatWarningsAndErrors g w e
    Info_Auto s -> f s "*Auto*"
    Info_Error _ s -> f s "*Error*"
    -- FNF: if Info_Warning comes back into use, the above should be
    -- clearWarning : f s "*Error*"
    --Info_Warning s -> [ display_warning "*Errors*" s ] -- FNF: currently unused
    Info_Time s -> f (render s) "*Time*"
    Info_NormalForm s -> f (render s) "*Normal Form*"   -- show?
    Info_InferredType s -> f (render s) "*Inferred Type*"
    Info_CurrentGoal s -> f (render s) "*Current Goal*"
    Info_GoalType s -> f (render s) "*Goal type etc.*"
    Info_ModuleContents s -> f (render s) "*Module contents*"
    Info_SearchAbout s -> f (render s) "*Search About*"
    Info_WhyInScope s -> f (render s) "*Scope Info*"
    Info_Context s -> f (render s) "*Context*"
    Info_HelperFunction s -> [ L [ A "agda2-info-action-and-copy"
                                 , A $ quote "*Helper function*"
                                 , A $ quote (render s ++ "\n")
                                 , A "nil"
                                 ]
                             ]
    Info_Intro s -> f (render s) "*Intro*"
    Info_Version -> f ("Agda version " ++ versionWithCommitInfo) "*Agda Version*"
  where f content bufname = [ display_info' False bufname content ]
lispifyResponse (Resp_ClearHighlighting tokenBased) =
  return [ L $ A "agda2-highlight-clear" :
               case tokenBased of
                 NotOnlyTokenBased -> []
                 TokenBased        ->
                   [ Q (lispifyTokenBased tokenBased) ]
         ]
lispifyResponse Resp_DoneAborting = return [ L [ A "agda2-abort-done" ] ]
lispifyResponse Resp_ClearRunningInfo = return [ clearRunningInfo ]
-- FNF: if Info_Warning comes back into use, the above should be
-- return [ clearRunningInfo, clearWarning ]
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
    prn (ii,e)= [showNumIId ii, A $ quote $ show e]

-- | Adds a \"last\" tag to a response.

lastTag :: Integer -> Lisp String -> Lisp String
lastTag n r = Cons (Cons (A "last") (A $ show n)) r

-- | Show an iteraction point identifier as an elisp expression.

showNumIId :: InteractionId -> Lisp String
showNumIId = A . tail . show
