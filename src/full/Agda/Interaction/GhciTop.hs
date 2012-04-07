{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, Rank2Types #-}
{-# OPTIONS -fno-cse #-}

module Agda.Interaction.GhciTop
  ( module Agda.Interaction.GhciTop
  , module Agda.Interaction.InteractionTop
  , module Agda.TypeChecker
  , module Agda.TypeChecking.MetaVars
  , module Agda.TypeChecking.Reduce
  , module Agda.TypeChecking.Errors

  , module Agda.Syntax.Position
  , module Agda.Syntax.Parser
--  , module SC  -- trivial clash removal: remove all!
--  , module SA
--  , module SI
  , module Agda.Syntax.Scope.Base
  , module Agda.Syntax.Scope.Monad
  , module Agda.Syntax.Translation.ConcreteToAbstract
  , module Agda.Syntax.Translation.AbstractToConcrete
  , module Agda.Syntax.Translation.InternalToAbstract
  , module Agda.Syntax.Abstract.Name

  , module Agda.Interaction.Exceptions

  , mkAbsolute
  )
  where

import System.Directory
import qualified System.IO as IO
import System.IO.Unsafe
import Data.IORef
import Control.Applicative hiding (empty)
import qualified Control.Exception as E

import Agda.Utils.Pretty
import Agda.Utils.String
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8

import Control.Monad.State
import Data.List as List
import Data.Maybe
import System.Exit

import Agda.TypeChecker
import Agda.TypeChecking.Monad as TM hiding (initState, setCommandLineOptions)
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors

import Agda.Syntax.Position
import Agda.Syntax.Parser
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract as SA
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding (bindName, withCurrentModule)
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete hiding (withScope)
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Name

import Agda.Interaction.InteractionTop
import Agda.Interaction.EmacsCommand hiding (putResponse)
import qualified Agda.Interaction.EmacsCommand as Emacs
import Agda.Interaction.Exceptions
import Agda.Interaction.Response
import Agda.Interaction.Highlighting.Emacs

#include "../undefined.h"
import Agda.Utils.Impossible

------------------------------------------

-- | The global state is needed only for the GHCi backend.

{-# NOINLINE theState #-}
theState :: IORef InteractionState
theState = unsafePerformIO $ newIORef $ emacsOutput initState

-- | Redirect the output to stdout in elisp format
--   suitable for the interactive emacs frontend.

emacsOutput :: InteractionState -> InteractionState
emacsOutput (InteractionState st cs) = InteractionState (st { stHighlightingOutput = emacsFormat }) cs

-- | Convert the response (to an interactive command)
--   to elisp expressions suitable for the interactive emacs frontend
--   and print it to stdout.

emacsFormat :: Response -> IO ()
emacsFormat = Emacs.putResponse <=< lispifyResponse

-- | Convert Response to an elisp value for the interactive emacs frontend.

lispifyResponse :: Response -> IO (Lisp String)
lispifyResponse (Resp_HighlightingInfo info) = return $ lispifyHighlightingInfo info
lispifyResponse (Resp_DisplayInfo info) = return $ case info of
    Info_CompilationOk -> f "The module was successfully compiled." "*Compilation result*"
    Info_Constraints s -> f s "*Constraints*"
    Info_AllGoals s -> f s "*All Goals*"
    Info_Auto s -> f s "*Auto*"
    Info_Error s -> f s "*Error*"

    Info_NormalForm s -> f (render s) "*Normal Form*"   -- show?
    Info_InferredType s -> f (render s) "*Inferred Type*"
    Info_CurrentGoal s -> f (render s) "*Current Goal*"
    Info_GoalType s -> f (render s) "*Goal type etc.*"
    Info_ModuleContents s -> f (render s) "*Module contents*"
    Info_Context s -> f (render s) "*Context*"
    Info_Intro s -> f (render s) "*Intro*"
  where f content bufname = display_info' False bufname content
lispifyResponse Resp_ClearRunningInfo = return $ clearRunningInfo
lispifyResponse (Resp_RunningInfo s) = return $ displayRunningInfo $ s ++ "\n"
lispifyResponse (Resp_Status s)
    = return $ L [ A "agda2-status-action"
                 , A (quote $ List.intercalate "," $ catMaybes [checked, showImpl])
                 ]
  where
    boolToMaybe b x = if b then Just x else Nothing

    checked  = boolToMaybe (sChecked               s) "Checked"
    showImpl = boolToMaybe (sShowImplicitArguments s) "ShowImplicit"

lispifyResponse (Resp_UpdateHighlighting info) = do
    dir <- getTemporaryDirectory
    f   <- E.bracket (IO.openTempFile dir "agda2-mode")
                   (IO.hClose . snd) $ \ (f, h) -> do
           UTF8.hPutStr h $ showHighlightingInfo info
           return f
    return $ L [ A "agda2-highlight-load-and-delete-action", A (quote f) ]
lispifyResponse (Resp_JumpToError f p)
    = return $ L [ A "agda2-goto", Q $ L [A (quote f), A ".", A (show p)] ]
lispifyResponse (Resp_InteractionPoints is) = return $
            Cons (Cons (A "last") (A "1"))
                 (L [ A "agda2-goals-action"
                    , Q $ L $ List.map showNumIId is
                    ])
lispifyResponse (Resp_GiveAction ii s)
    = return $ L [A "agda2-give-action", showNumIId ii, A s']
  where
    s' = case s of
        Give_String str -> quote str
        Give_Paren      -> "'paren"
        Give_NoParen    -> "'no-paren"
lispifyResponse (Resp_MakeCaseAction cs) = return $
     Cons (Cons (A "last") (A "2"))
          (L [ A "agda2-make-case-action",
               Q $ L $ List.map (A . quote) cs
             ])
lispifyResponse (Resp_MakeCase cmd pcs) = return $
      Cons (Cons (A "last") (A "2"))
           (L [ A cmd
              , Q $ L $ List.map (A . quote) pcs
              ])
lispifyResponse (Resp_SolveAll ps) = return $
    Cons (Cons (A "last") (A "2"))
         (L [ A "agda2-solveAll-action"
            , Q . L $ concatMap prn ps
            ])
  where
    prn (ii,e)= [showNumIId ii, A $ quote $ show e]

-- | Show an iteraction point identifier as an elisp expression.
showNumIId :: InteractionId -> Lisp String
showNumIId = A . tail . show


-- | Run a TCM computation in the current state. Should only
--   be used for debugging.

ioTCM_ :: TCM a -> IO a
ioTCM_ m = do
  InteractionState tcs cs <- readIORef theState
  result <- runTCM $ do
    put tcs
    x <- withEnv (initEnv { envEmacs = True }) m
    tcs <- get
    return (x, tcs)
  case result of
    Right (x, tcs) -> do
      writeIORef theState $ InteractionState tcs cs
      return x
    Left err -> do
      Right doc <- runTCM $ prettyTCM err
      putStrLn $ render doc
      return __IMPOSSIBLE__
{-
  Right (x, s) <- runTCM $ do
    put $ theTCState tcs
    x <- withEnv initEnv m
    s <- get
    return (x, s)
  writeIORef theState $ tcs { theTCState = s }
  return x
-}

-- | Runs a 'TCM' computation. All calls from the Emacs mode should be
--   wrapped in this function.

ioTCM :: FilePath
         -- ^ The current file. If this file does not match
         -- 'theCurrentFile, and the 'Interaction' is not
         -- \"independent\", then an error is raised.
      -> Bool
         -- ^ Should syntax highlighting information be produced? In
         -- that case this function will generate an Emacs command
         -- which interprets this information.
      -> Interaction
      -> IO ()
ioTCM current highlighting cmd = do
#if MIN_VERSION_base(4,2,0)
  -- Ensure that UTF-8 is used for communication with the Emacs mode.
  IO.hSetEncoding IO.stdout IO.utf8
#endif

  -- Read the state.
  state <- readIORef theState

  response <- ioTCMState current highlighting cmd $ emacsOutput state

  -- Write the state or halt with an error.
  case response of
    Just state -> writeIORef theState state
    Nothing ->    exitWith (ExitFailure 1)


-- Helpers for testing ----------------------------------------------------

getCurrentFile :: IO FilePath
getCurrentFile = do
  mf <- (theCurrentFile . theCommandState) <$> readIORef theState
  case mf of
    Nothing     -> error "command: No file loaded!"
    Just (f, _) -> return (filePath f)

top_command' :: FilePath -> Interaction -> IO ()
top_command' f cmd = ioTCM f False cmd

goal_command :: InteractionId -> GoalCommand -> String -> IO ()
goal_command i cmd s = do
  f <- getCurrentFile
  -- TODO: Test with other ranges as well.
  ioTCM f False $ cmd i noRange s
