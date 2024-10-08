{-# LANGUAGE NondecreasingIndentation #-}
{-# OPTIONS_GHC -fno-cse #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Interaction.InteractionTop
  ( module Agda.Interaction.InteractionTop
  )
  where

import Prelude hiding (null)

import Control.Concurrent
import Control.Concurrent.Async
import Control.Concurrent.STM.TChan
import Control.Concurrent.STM.TVar
import qualified Control.Exception  as E

import Control.Monad.Except         ( MonadError(..), ExceptT(..), runExceptT )
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.State          ( MonadState(..), gets, modify, runStateT )
import Control.Monad.STM
import Control.Monad.State          ( StateT )

import qualified Data.Char as Char
import Data.Function (on)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe

import System.Directory
import System.FilePath

import Agda.TypeChecking.Monad as TCM
  hiding (initState, setCommandLineOptions)
import qualified Agda.TypeChecking.Monad as TCM
import qualified Agda.TypeChecking.Pretty as TCP
import Agda.TypeChecking.Rules.Term (checkExpr, isType_)
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings (warning)

import Agda.Syntax.Fixity
import Agda.Syntax.Position
import Agda.Syntax.Parser
import Agda.Syntax.Common
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Glyph
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Info (mkDefInfo)
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Scope.Base
import Agda.Syntax.TopLevelModuleName

import Agda.Interaction.Base
import Agda.Interaction.ExitCode (pattern TCMError, exitAgdaWith)
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses as Lenses
import Agda.Interaction.MakeCase
import Agda.Interaction.SearchAbout
import Agda.Interaction.Response hiding (Function, ExtendedLambda)
import qualified Agda.Interaction.Response as R
import qualified Agda.Interaction.BasicOps as B
import Agda.Interaction.Highlighting.Precise hiding (Error, Postulate, singleton)
import Agda.Interaction.Imports  ( Mode, pattern ScopeCheck, pattern TypeCheck )
import qualified Agda.Interaction.Imports as Imp
import Agda.Interaction.Highlighting.Generate

import Agda.Compiler.Backend

import Agda.Mimer.Mimer as Mimer
import qualified Control.DeepSeq as DeepSeq

import Agda.Utils.Either
import Agda.Utils.FileName
import Agda.Utils.Function
import Agda.Utils.Hash
import Agda.Utils.IO (showIOException)
import Agda.Utils.Lens
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty hiding (Mode)
import qualified Agda.Utils.ProfileOptions as Profile
import Agda.Utils.Singleton
import Agda.Utils.String
import Agda.Utils.Time
import Agda.Utils.Tuple
import Agda.Utils.WithDefault (lensCollapseDefault, lensKeepDefault)

import Agda.Utils.Impossible
import Agda.TypeChecking.Opacity (saturateOpaqueBlocks)

------------------------------------------------------------------------
-- The CommandM monad

type CommandM = StateT CommandState TCM

-- | Restore both 'TCState' and 'CommandState'.

localStateCommandM :: CommandM a -> CommandM a
localStateCommandM m = do
  cSt <- get
  tcSt <- getTC
  x <- m
  putTC tcSt
  put cSt
  return x

-- | Restore 'TCState', do not touch 'CommandState'.

liftLocalState :: TCM a -> CommandM a
liftLocalState = lift . localTCState

-- | Build an opposite action to 'lift' for state monads.

revLift
    :: MonadState st m
    => (forall c . m c -> st -> k (c, st))      -- ^ run
    -> (forall b . k b -> m b)                  -- ^ lift
    -> (forall x . (m a -> k x) -> k x) -> m a  -- ^ reverse lift in double negative position
revLift run lift' f = do
    st <- get
    (a, st') <- lift' $ f (`run` st)
    put st'
    return a

revLiftTC
    :: MonadTCState m
    => (forall c . m c -> TCState -> k (c, TCState))  -- ^ run
    -> (forall b . k b -> m b)                        -- ^ lift
    -> (forall x . (m a -> k x) -> k x) -> m a        -- ^ reverse lift in double negative position
revLiftTC run lift' f = do
    st <- getTC
    (a, st') <- lift' $ f (`run` st)
    putTC st'
    return a

-- | Opposite of 'liftIO' for 'CommandM'.
--
-- This function should only be applied to computations that are
-- guaranteed not to raise any errors (except for 'IOException's).

commandMToIO :: (forall x . (CommandM a -> IO x) -> IO x) -> CommandM a
commandMToIO ci_i = revLift runStateT lift $ \ct -> revLiftTC runSafeTCM liftIO $ ci_i . (. ct)

-- | Lift a TCM action transformer to a CommandM action transformer.

liftCommandMT :: (forall x . TCM x -> TCM x) -> CommandM a -> CommandM a
liftCommandMT f m = revLift runStateT lift $ f . ($ m)

-- | Ditto, but restore state.

liftCommandMTLocalState :: (forall x . TCM x -> TCM x) -> CommandM a -> CommandM a
liftCommandMTLocalState f = liftCommandMT f . localStateCommandM

-- | Put a response by the callback function given by 'stInteractionOutputCallback'.

putResponse :: Response -> CommandM ()
putResponse = lift . appInteractionOutputCallback


-- | A Lens for 'theInteractionPoints'.

modifyTheInteractionPoints :: ([InteractionId] -> [InteractionId]) -> CommandM ()
modifyTheInteractionPoints f = modify $ \ s ->
  s { theInteractionPoints = f (theInteractionPoints s) }


-- * Operations for manipulating 'oldInteractionScopes'.

-- | A Lens for 'oldInteractionScopes'.
modifyOldInteractionScopes :: (OldInteractionScopes -> OldInteractionScopes) -> CommandM ()
modifyOldInteractionScopes f = modify $ \ s ->
  s { oldInteractionScopes = f $ oldInteractionScopes s }

insertOldInteractionScope :: InteractionId -> ScopeInfo -> CommandM ()
insertOldInteractionScope ii scope = do
  lift $ reportSLn "interaction.scope" 20 $ "inserting old interaction scope " ++ show ii
  modifyOldInteractionScopes $ Map.insert ii scope

removeOldInteractionScope :: InteractionId -> CommandM ()
removeOldInteractionScope ii = do
  lift $ reportSLn "interaction.scope" 20 $ "removing old interaction scope " ++ show ii
  modifyOldInteractionScopes $ Map.delete ii

getOldInteractionScope :: InteractionId -> CommandM ScopeInfo
getOldInteractionScope ii = do
  ms <- gets $ Map.lookup ii . oldInteractionScopes
  case ms of
    Nothing    -> __IMPOSSIBLE_VERBOSE__ $ "not an old interaction point: " ++ show ii
    Just scope -> return scope

-- | Do setup and error handling for a command.

handleCommand_ :: CommandM () -> CommandM ()
handleCommand_ = handleCommand id (return ())

handleCommand :: (forall a. CommandM a -> CommandM a) -> CommandM () -> CommandM () -> CommandM ()
handleCommand wrap onFail cmd = handleNastyErrors $ wrap $ do
    oldState <- getTC

    -- -- Andreas, 2016-11-18 OLD CODE:
    -- -- onFail and handleErr are executed in "new" command state (not TCState).
    -- -- But it seems that if an exception is raised, it is identical to the old state,
    -- -- see code for catchErr.
    -- res <- (`catchErr` (return . Just)) $ Nothing <$ cmd
    -- maybe (return ()) (\ e -> onFail >> handleErr e) res

    -- Andreas, 2016-11-18 NEW CODE: execute onFail and handleErr in handler
    -- which means (looking at catchErr) they run in state s rathern than s'.
    -- Yet, it looks like s == s' in case the command failed.
    cmd `catchErr` \ e -> do
      onFail
      handleErr Nothing e
      -- Andreas, 2016-11-18, issue #2174
      -- Reset TCState after error is handled, to get rid of metas created during failed command
      lift $ do
        newPersistentState <- useTC lensPersistentState
        putTC oldState
        lensPersistentState `setTCLens` newPersistentState

  where
    -- Preserves state so we can do unsolved meta highlighting
    catchErr :: CommandM a -> (TCErr -> CommandM a) -> CommandM a
    catchErr m h = do
      s       <- get
      (x, s') <- lift $ do runStateT m s
         `catchError_` \ e ->
           runStateT (h e) s
      put s'
      return x

    -- Handle every possible kind of error (#637), except for
    -- AsyncCancelled, which is used to abort Agda.
    handleNastyErrors :: CommandM () -> CommandM ()
    handleNastyErrors m = commandMToIO $ \ toIO -> do

      let asyncHandler e@AsyncCancelled = return (Left e)

          ioHandler (e :: E.IOException) = Right <$> do
            toIO $ handleErr (Just Direct) $ IOException Nothing noRange e

          generalHandler (e :: E.SomeException) = Right <$> do
            toIO $ handleErr (Just Direct) $ GenericException $ showIOException e

      r <- (Right <$> toIO m)
             `E.catch` asyncHandler
             `E.catch` ioHandler
             `E.catch` generalHandler
      case r of
        Right x -> return x
        Left e  -> E.throwIO e

    -- Displays an error and instructs Emacs to jump to the site of the
    -- error. Because this function may switch the focus to another file
    -- the status information is also updated.
    handleErr method e = do

      -- TODO: make a better predicate for this
      noError <- lift $ null <$> renderError e
      unless noError do

        unsolved <- lift $ computeUnsolvedInfo
        err     <- lift $ errorHighlighting e
        modFile <- lift $ useTC stModuleToSource
        method  <- case method of
          Nothing -> lift $ viewTC eHighlightingMethod
          Just m  -> return m
        let info = convert $ err <> unsolved
                     -- Errors take precedence over unsolved things.

        showImpl <- lift $ optShowImplicit <$> useTC stPragmaOptions
        showIrr <- lift $ optShowIrrelevant <$> useTC stPragmaOptions
        do
          mapM_ putResponse $
            [ Resp_DisplayInfo $ Info_Error $ Info_GenericError e ] ++
            tellEmacsToJumpToError (getRange e) ++
            [ Resp_HighlightingInfo info KeepHighlighting
                                    method modFile ] ++
            [ Resp_Status $ Status { sChecked = False
                                   , sShowImplicitArguments = showImpl
                                   , sShowIrrelevantArguments = showIrr
                                   } ]
          whenM (optExitOnError <$> commandLineOptions) $
            liftIO $ exitAgdaWith TCMError

-- | Run an 'IOTCM' value, catch the exceptions, emit output
--
--   If an error happens the state of 'CommandM' does not change,
--   but stPersistent may change (which contains successfully
--   loaded interfaces for example).

runInteraction :: IOTCM -> CommandM ()
runInteraction iotcm =
  handleCommand inEmacs onFail $ do
    currentAbs <- liftIO $ absolute current
    cf  <- gets theCurrentFile
    cmd <- if independent cmd then return cmd else do
      when (Just currentAbs /= (currentFilePath <$> cf)) $ do
        let mode = TypeCheck
        cmd_load' current [] True mode $ \_ -> return ()
      cf <- fromMaybe __IMPOSSIBLE__ <$> gets theCurrentFile
      return $ case iotcm (Just (currentFileModule cf)) of
        IOTCM _ _ _ cmd -> cmd

    withCurrentFile $ interpret cmd

    cf' <- gets theCurrentFile
    when (updateInteractionPointsAfter cmd
            &&
          Just currentAbs == (currentFilePath <$> cf')) $ do
        putResponse . Resp_InteractionPoints =<< gets theInteractionPoints

  where
    -- The ranges in cmd might be incorrect because of the use of
    -- Nothing here. That is taken care of above.
    IOTCM current highlighting highlightingMethod cmd = iotcm Nothing

    inEmacs :: forall a. CommandM a -> CommandM a
    inEmacs = liftCommandMT $ withEnv $ initEnv
            { envHighlightingLevel  = highlighting
            , envHighlightingMethod = highlightingMethod
            }

    -- If an independent command fails we should reset theCurrentFile (Issue853).
    onFail | independent cmd = modify $ \ s -> s { theCurrentFile = Nothing }
           | otherwise       = return ()

------------------------------------------------------------------------
-- Command queues

-- | If the next command from the command queue is anything but an
-- actual command, then the command is returned.
--
-- If the command is an 'IOTCM' command, then the following happens:
-- The given computation is applied to the command and executed. If an
-- abort command is encountered (and acted upon), then the computation
-- is interrupted, the persistent state and all options are restored,
-- and some commands are sent to the frontend. If the computation was
-- not interrupted, then its result is returned.

-- TODO: It might be nice if some of the changes to the persistent
-- state inflicted by the interrupted computation were preserved.

maybeAbort :: (IOTCM -> CommandM a) -> CommandM (Command' (Maybe a))
maybeAbort m = do
  commandState <- get
  let q = commandQueue commandState
  (n, cmd) <- liftIO $ atomically $ readTChan (commands q)
  case cmd of
    Done      -> return Done
    Error e   -> return (Error e)
    Command c -> do
      tcState <- getTC
      tcEnv   <- askTC
      result  <- liftIO $ race
                   (runTCM tcEnv tcState $
                    runStateT (m c) commandState)
                   (waitForAbort n q)
      case result of
        Left ((x, commandState'), tcState') -> do
          putTC tcState'
          put commandState'
          case c Nothing of
            IOTCM _ _ _ Cmd_exit -> do
              putResponse Resp_DoneExiting
              return Done
            _ -> return (Command (Just x))
        Right a -> do
          liftIO $ popAbortedCommands q a
          putTC $ initState
            { stPersistentState = stPersistentState tcState
            , stPreScopeState   =
                (stPreScopeState initState)
                  { stPrePragmaOptions =
                      stPrePragmaOptions
                        (stPreScopeState tcState)
                  }
            }
          put $ (initCommandState (commandQueue commandState))
            { optionsOnReload = optionsOnReload commandState
            }
          putResponse Resp_DoneAborting
          displayStatus
          return (Command Nothing)
  where

  -- Returns if the currently executing command should be aborted.
  -- The "abort number" is returned.

  waitForAbort
    :: Integer       -- The number of the currently executing command.
    -> CommandQueue  -- The command queue.
    -> IO Integer
  waitForAbort n q = do
    atomically $ do
      a <- readTVar (abort q)
      case a of
        Just a' | n <= a' -> return a'
        _                 -> retry

  -- Removes every command for which the command number is at most
  -- the given number (the "abort number") from the command queue.
  --
  -- New commands could be added to the end of the queue while this
  -- computation is running. This does not lead to a race condition,
  -- because those commands have higher command numbers, so they will
  -- not be removed.

  popAbortedCommands :: CommandQueue -> Integer -> IO ()
  popAbortedCommands q n = do
    done <- atomically $ do
      cmd <- tryReadTChan (commands q)
      case cmd of
        Nothing -> return True
        Just c  ->
          if fst c <= n then
            return False
           else do
            unGetTChan (commands q) c
            return True
    unless done $
      popAbortedCommands q n

-- | Creates a command queue, and forks a thread that writes commands
-- to the queue. The queue is returned.

initialiseCommandQueue
  :: IO Command
     -- ^ Returns the next command.
  -> IO CommandQueue
initialiseCommandQueue next = do
  commands <- newTChanIO
  abort    <- newTVarIO Nothing

  let -- Read commands. The argument is the number of the previous
      -- command (other than abort commands) that was read, if any.
      readCommands n = do
        c <- next
        case c of
          Command c | IOTCM _ _ _ Cmd_abort <- c Nothing -> do
            atomically $ writeTVar abort (Just n)
            readCommands n
          _ -> do
            let n' = (succ n)
            atomically $ writeTChan commands (n', c)
            case c of
              Done -> return ()
              _    -> readCommands n'

  _ <- forkIO (readCommands 0)

  return (CommandQueue { .. })

---------------------------------------------------------

-- | Can the command run even if the relevant file has not been loaded
--   into the state?

independent :: Interaction -> Bool
independent (Cmd_load {})                   = True
independent Cmd_load_no_metas{}             = True
independent (Cmd_compile {})                = True
independent (Cmd_load_highlighting_info {}) = True
independent Cmd_tokenHighlighting {}        = True
independent Cmd_show_version                = True
independent _                               = False

-- | Should 'Resp_InteractionPoints' be issued after the command has
-- run?

updateInteractionPointsAfter :: Interaction -> Bool
updateInteractionPointsAfter Cmd_load{}                          = True
updateInteractionPointsAfter Cmd_compile{}                       = True
updateInteractionPointsAfter Cmd_constraints{}                   = False
updateInteractionPointsAfter Cmd_metas{}                         = False
updateInteractionPointsAfter Cmd_load_no_metas{}                 = False
updateInteractionPointsAfter Cmd_show_module_contents_toplevel{} = False
updateInteractionPointsAfter Cmd_search_about_toplevel{}         = False
updateInteractionPointsAfter Cmd_solveAll{}                      = True
updateInteractionPointsAfter Cmd_solveOne{}                      = True
updateInteractionPointsAfter Cmd_infer_toplevel{}                = False
updateInteractionPointsAfter Cmd_compute_toplevel{}              = False
updateInteractionPointsAfter Cmd_load_highlighting_info{}        = False
updateInteractionPointsAfter Cmd_tokenHighlighting{}             = False
updateInteractionPointsAfter Cmd_highlight{}                     = True
updateInteractionPointsAfter ShowImplicitArgs{}                  = False
updateInteractionPointsAfter ToggleImplicitArgs{}                = False
updateInteractionPointsAfter ShowIrrelevantArgs{}                = False
updateInteractionPointsAfter ToggleIrrelevantArgs{}              = False
updateInteractionPointsAfter Cmd_give{}                          = True
updateInteractionPointsAfter Cmd_refine{}                        = True
updateInteractionPointsAfter Cmd_intro{}                         = True
updateInteractionPointsAfter Cmd_refine_or_intro{}               = True
updateInteractionPointsAfter Cmd_autoOne{}                       = True
updateInteractionPointsAfter Cmd_autoAll{}                       = True
updateInteractionPointsAfter Cmd_context{}                       = False
updateInteractionPointsAfter Cmd_helper_function{}               = False
updateInteractionPointsAfter Cmd_infer{}                         = False
updateInteractionPointsAfter Cmd_goal_type{}                     = False
updateInteractionPointsAfter Cmd_elaborate_give{}                = True
updateInteractionPointsAfter Cmd_goal_type_context{}             = False
updateInteractionPointsAfter Cmd_goal_type_context_infer{}       = False
updateInteractionPointsAfter Cmd_goal_type_context_check{}       = False
updateInteractionPointsAfter Cmd_show_module_contents{}          = False
updateInteractionPointsAfter Cmd_make_case{}                     = True
updateInteractionPointsAfter Cmd_compute{}                       = False
updateInteractionPointsAfter Cmd_why_in_scope{}                  = False
updateInteractionPointsAfter Cmd_why_in_scope_toplevel{}         = False
updateInteractionPointsAfter Cmd_show_version{}                  = False
updateInteractionPointsAfter Cmd_abort{}                         = False
updateInteractionPointsAfter Cmd_exit{}                          = False

-- | Interpret an interaction

interpret :: Interaction -> CommandM ()

interpret (Cmd_load m argv) =
  cmd_load' m argv True mode $ \_ -> interpret $ Cmd_metas AsIs
  where
  mode = TypeCheck

interpret (Cmd_compile backend file argv) =
  cmd_load' file argv allowUnsolved mode $ \ checkResult -> do
    ws <- lift $ applyFlagsToTCWarnings $ crWarnings checkResult
    case null ws of
      True -> do
        lift $ case backend of
          LaTeX                    -> callBackend "LaTeX" IsMain checkResult
          QuickLaTeX               -> callBackend "LaTeX" IsMain checkResult
          OtherBackend "GHCNoMain" -> callBackend "GHC" NotMain checkResult   -- for backwards compatibility
          OtherBackend b           -> callBackend b IsMain checkResult
        display_info . Info_CompilationOk backend =<< lift B.getWarningsAndNonFatalErrors
      False -> display_info $ Info_Error $ Info_CompilationError ws
  where
  allowUnsolved = backend `elem` [LaTeX, QuickLaTeX]
  mode | QuickLaTeX <- backend = ScopeCheck
       | otherwise             = TypeCheck

interpret Cmd_constraints =
    display_info . Info_Constraints =<< lift B.getConstraints

interpret (Cmd_metas norm) = do
  ms <- lift $ B.getGoals' norm (max Simplified norm)
  display_info . Info_AllGoalsWarnings ms =<< lift B.getWarningsAndNonFatalErrors

interpret (Cmd_load_no_metas file) = do
  -- Fail if there are open metas.
  let allowMetas = False
  cmd_load' file [] allowMetas TypeCheck $ \ result -> do
    Imp.raiseNonFatalErrors result
    unlessM (null <$> getOpenMetas) __IMPOSSIBLE__

interpret (Cmd_show_module_contents_toplevel norm s) =
  atTopLevel $ showModuleContents norm noRange s

interpret (Cmd_search_about_toplevel norm s) =
  atTopLevel $ searchAbout norm noRange s

interpret (Cmd_solveAll norm)        = solveInstantiatedGoals norm Nothing
interpret (Cmd_solveOne norm ii _ _) = solveInstantiatedGoals norm' (Just ii)
  -- `solveOne` is called via `agda2-maybe-normalised` which does not use
  -- AsIs < Simplified < Normalised but rather Simplified < Instantiated < Normalised
  -- So we remap the Rewrite modifiers to match solveAll's behaviour.
  -- NB: instantiate is called in getSolvedInteractionPoints no matter what.
  where norm' = case norm of
                  Simplified   -> AsIs
                  Instantiated -> Simplified
                  _            -> norm

interpret (Cmd_infer_toplevel norm s) = do
  (time, expr) <- parseAndDoAtToplevel (B.typeInCurrent norm) s
  state <- get
  display_info $ Info_InferredType state time expr

interpret (Cmd_compute_toplevel cmode s) = do
  (time, expr) <- parseAndDoAtToplevel action (B.computeWrapInput cmode s)
  state <- get
  display_info $ Info_NormalForm state cmode time expr
    where
    action = allowNonTerminatingReductions
           . (if B.computeIgnoreAbstract cmode then ignoreAbstractMode else inConcreteMode)
           . B.evalInCurrent cmode
-- interpret (Cmd_compute_toplevel cmode s) =
--   parseAndDoAtToplevel action Info_NormalForm $ computeWrapInput cmode s
--   where
--   action = allowNonTerminatingReductions
--          . (if computeIgnoreAbstract cmode then ignoreAbstractMode else inConcreteMode)
--          . (B.showComputed cmode <=< B.evalInCurrent)


interpret (ShowImplicitArgs showImpl) = do
  opts <- lift commandLineOptions
  setCommandLineOpts $
    set (lensPragmaOptions . lensOptShowImplicit . lensKeepDefault) showImpl opts

interpret ToggleImplicitArgs = do
  opts <- lift commandLineOptions
  setCommandLineOpts $
    over (lensPragmaOptions . lensOptShowImplicit . lensCollapseDefault) not opts

interpret (ShowIrrelevantArgs showIrr) = do
  opts <- lift commandLineOptions
  setCommandLineOpts $
    set (lensPragmaOptions . lensOptShowIrrelevant . lensKeepDefault) showIrr opts

interpret ToggleIrrelevantArgs = do
  opts <- lift commandLineOptions
  setCommandLineOpts $
    over (lensPragmaOptions . lensOptShowIrrelevant . lensCollapseDefault) not opts

interpret (Cmd_load_highlighting_info source) = do
  l <- asksTC envHighlightingLevel
  when (l /= None) $ do
    -- Make sure that the include directories have
    -- been set.
    setCommandLineOpts =<< lift commandLineOptions
    resp <- lift $ liftIO . tellToUpdateHighlighting =<< do
      ex        <- liftIO $ doesFileExist source
      absSource <- liftIO $ SourceFile <$> absolute source
      if ex
        then
           do
              src <- Imp.parseSource absSource
              let m = Imp.srcModuleName src
              checkModuleName m absSource Nothing
              mmi <- getVisitedModule m
              case mmi of
                Nothing -> return Nothing
                Just mi ->
                  if hashText (Imp.srcText src) == iSourceHash (miInterface mi)
                    then do
                      modFile <- useTC stModuleToSource
                      method  <- viewTC eHighlightingMethod
                      return $ Just (iHighlighting $ miInterface mi, method, modFile)
                    else
                      return Nothing
            `catchError` \_ -> return Nothing
        else
          return Nothing
    mapM_ putResponse resp

interpret (Cmd_tokenHighlighting source remove) = do
  info <- do l <- asksTC envHighlightingLevel
             if l == None
               then return Nothing
               else do
                 source' <- liftIO (absolute source)
                 lift $ (Just <$> generateTokenInfo source')
                           `catchError` \_ ->
                        return Nothing
      `finally`
    case remove of
      Remove -> liftIO $ removeFile source
      Keep   -> return ()
  case info of
    Just info' -> lift $ printHighlightingInfo RemoveHighlighting info'
    Nothing    -> return ()

interpret (Cmd_highlight ii rng s) = do
  l <- asksTC envHighlightingLevel
  when (l /= None) $ do
    scope <- getOldInteractionScope ii
    removeOldInteractionScope ii
    handle $ do
      parsed <- try (Info_HighlightingParseError ii) $
             B.parseExpr rng s
      expr <- try (Info_HighlightingScopeCheckError ii) $
             concreteToAbstract scope parsed
      lift $ printHighlightingInfo KeepHighlighting =<<
               generateTokenInfoFromString rng s
      lift $ highlightExpr expr
  where
    handle :: ExceptT Info_Error TCM () -> CommandM ()
    handle m = do
      res <- lift $ runExceptT m
      case res of
        Left err -> display_info $ Info_Error err
        Right _ -> return ()
    try :: Info_Error -> TCM a -> ExceptT Info_Error TCM a
    try err m = ExceptT $ do
      (mapLeft (const err) <$> freshTCM m) `catchError` \ _ -> return (Left err)
      -- freshTCM to avoid scope checking creating new interaction points

interpret (Cmd_give   force ii rng s) = give_gen force ii rng s Give
interpret (Cmd_refine ii rng s) = give_gen WithoutForce ii rng s Refine

interpret (Cmd_intro pmLambda ii rng _) = do
  ss <- lift $ B.introTactic pmLambda ii
  liftCommandMT (withInteractionId ii) $ case ss of
    []    -> do
      display_info $ Info_Intro_NotFound
    [s]   -> give_gen WithoutForce ii rng s Intro
    _:_:_ -> do
      display_info $ Info_Intro_ConstructorUnknown ss

interpret (Cmd_refine_or_intro pmLambda ii r s) = interpret $
  let s' = trim s
  in (if null s' then Cmd_intro pmLambda else Cmd_refine) ii r s'

interpret (Cmd_autoOne norm ii rng str) = do
  iscope <- getInteractionScope ii
  (time, result) <- maybeTimed $ Mimer.mimer norm ii rng str
  case result of
    MimerNoResult -> display_info $ Info_Auto "No solution found"
    MimerExpr str -> do
      insertOldInteractionScope ii iscope
      putResponse $ Resp_GiveAction ii $ Give_String str
      modifyTheInteractionPoints (List.delete ii)
      maybe (return ()) (display_info . Info_Time) time
    MimerList sols -> do
      display_info $ Info_Auto $ unlines $
        [ "Solutions:" ] ++
        [ "  " ++ show i ++ ". " ++ s | (i, s) <- sols ]
    MimerClauses{} -> __IMPOSSIBLE__    -- Mimer can't do case splitting yet

interpret (Cmd_autoAll norm) = do
  iis <- getInteractionPoints
  getOldScope <- do
    st <- getTC
    pure $ \ ii -> liftLocalState $ putTC st >> getInteractionScope ii
  unless (null iis) $ do
    let time = 1000 `div` length iis
    st <- getTC
    solved <- fmap concat $ forM iis $ \ ii -> do
      rng <- getInteractionRange ii
      res <- Mimer.mimer norm ii rng ("-t " ++ show time ++ "ms")
      case res of
        MimerNoResult -> pure []
        MimerExpr str -> do
          insertOldInteractionScope ii =<< getOldScope ii
          putResponse $ Resp_GiveAction ii $ Give_String str
          pure [ii]
        MimerList{} -> pure []    -- Don't list solutions in autoAll
        MimerClauses{} -> __IMPOSSIBLE__  -- Mimer can't do case splitting yet
    modifyTheInteractionPoints (List.\\ solved)

interpret (Cmd_context norm ii _ _) =
  display_info . Info_Context ii =<< liftLocalState (B.getResponseContext norm ii)

interpret (Cmd_helper_function norm ii rng s) = do
  -- Create type of application of new helper function that would solve the goal.
  helperType <- liftLocalState $ withInteractionId ii $ inTopContext $ B.metaHelperType norm ii rng s
  display_info $ Info_GoalSpecific ii (Goal_HelperFunction helperType)

interpret (Cmd_infer norm ii rng s) = do
  expr <- liftLocalState $ withInteractionId ii $ B.typeInMeta ii norm =<< B.parseExprIn ii rng s
  display_info $ Info_GoalSpecific ii (Goal_InferredType expr)

interpret (Cmd_goal_type norm ii _ _) =
  display_info $ Info_GoalSpecific ii (Goal_CurrentGoal norm)

interpret (Cmd_elaborate_give norm ii rng s) =
  give_gen WithoutForce ii rng s $ ElaborateGive norm

interpret (Cmd_goal_type_context norm ii rng s) =
  cmd_goal_type_context_and GoalOnly norm ii rng s

interpret (Cmd_goal_type_context_infer norm ii rng s) = do
  -- In case of the empty expression to type, don't fail with
  -- a stupid parse error, but just fall back to
  -- Cmd_goal_type_context.
  aux <- if all Char.isSpace s
            then return GoalOnly
            else do
              liftLocalState $ withInteractionId ii $ do
                parsed <- B.parseExprIn ii rng s
                (typ, faces) <- B.typeAndFacesInMeta ii norm parsed
                return (GoalAndHave typ faces)
  cmd_goal_type_context_and aux norm ii rng s

interpret (Cmd_goal_type_context_check norm ii rng s) = do
  term <- liftLocalState $ withInteractionId ii $ do
    expr <- B.parseExprIn ii rng s
    goal <- B.typeOfMeta AsIs ii
    term <- case goal of
      OfType _ ty -> checkExpr expr =<< isType_ ty
      _           -> __IMPOSSIBLE__
    B.normalForm norm term
  cmd_goal_type_context_and (GoalAndElaboration term) norm ii rng s

interpret (Cmd_show_module_contents norm ii rng s) =
  liftCommandMT (withInteractionId ii) $ showModuleContents norm rng s

interpret (Cmd_why_in_scope_toplevel s) =
  atTopLevel $ whyInScope s

interpret (Cmd_why_in_scope ii _range s) =
  liftCommandMT (withInteractionId ii) $ whyInScope s

interpret (Cmd_make_case ii rng s) = do
  (f, casectxt, cs) <- lift $ makeCase ii rng s
  liftCommandMT (withInteractionId ii) $ do
    tel <- lift $ lookupSection (qnameModule f) -- don't shadow the names in this telescope
    unicode <- getsTC $ optUseUnicode . getPragmaOptions
    pcs      :: [Doc]      <- lift $ inTopContext $ addContext tel $ mapM prettyA cs
    let pcs' :: [String]    = List.map (extlam_dropName unicode casectxt . decorate) pcs
    lift $ reportSDoc "interaction.case" 60 $ TCP.vcat
      [ "InteractionTop.Cmd_make_case"
      , TCP.nest 2 $ TCP.vcat
        [ "cs   = " TCP.<+> TCP.vcat (map prettyA cs)
        , "pcs  = " TCP.<+> TCP.vcat (map return pcs)
        , "pcs' = " TCP.<+> TCP.vcat (map TCP.text pcs')
        ]
      ]
    lift $ reportSDoc "interaction.case" 90 $ TCP.vcat
      [ "InteractionTop.Cmd_make_case"
      , TCP.nest 2 $ TCP.vcat
        [ "cs   = " TCP.<+> TCP.text (show cs)
        ]
      ]
    putResponse $ Resp_MakeCase ii (makeCaseVariant casectxt) pcs'


interpret (Cmd_compute cmode ii rng s) = do
  expr <- liftLocalState $ do
    e <- B.parseExprIn ii rng $ B.computeWrapInput cmode s
    withInteractionId ii $ applyWhen (B.computeIgnoreAbstract cmode) ignoreAbstractMode $ B.evalInCurrent cmode e
  display_info $ Info_GoalSpecific ii (Goal_NormalForm cmode expr)

interpret Cmd_show_version = display_info Info_Version

interpret Cmd_abort = return ()
interpret Cmd_exit  = return ()


decorate :: Doc -> String
decorate = renderStyle (style { mode = OneLineMode })

makeCaseVariant :: CaseContext -> MakeCaseVariant
makeCaseVariant Nothing = R.Function
makeCaseVariant Just{}  = R.ExtendedLambda

-- very dirty hack, string manipulation by dropping the function name
-- and replacing the last " = " with " -> ". It's important not to replace
-- the equal sign in named implicit with an arrow!
extlam_dropName :: UnicodeOrAscii -> CaseContext -> String -> String
extlam_dropName _ Nothing x = x
extlam_dropName glyphMode Just{}  x
    = unwords $ reverse $ replEquals $ reverse $ drop 1 $ words x
  where
    arrow = render $ _arrow $ specialCharactersForGlyphs glyphMode
    replEquals ("=" : ws) = arrow : ws
    replEquals (w   : ws) = w : replEquals ws
    replEquals []         = []

-- | Solved goals already instantiated internally
-- The second argument potentially limits it to one specific goal.
solveInstantiatedGoals :: Rewrite -> Maybe InteractionId -> CommandM ()
solveInstantiatedGoals norm mii = do
  -- Andreas, 2016-10-23 issue #2280: throw away meta elims.
  out <- lift $ localTC (\ e -> e { envPrintMetasBare = True }) $ do
    sip <- B.getSolvedInteractionPoints False norm
           -- only solve metas which have a proper instantiation, i.e., not another meta
    let sip' = maybe id (\ ii -> filter ((ii ==) . fst3)) mii sip
    mapM prt sip'
  putResponse $ Resp_SolveAll out
  where
      prt (i, m, e) = do
        mi <- getMetaInfo <$> lookupLocalMeta m
        e' <- withMetaInfo mi $ abstractToConcreteCtx TopCtx e
        return (i, e')

-- | @cmd_load' file argv unsolvedOk cmd@
--   loads the module in file @file@,
--   using @argv@ as the command-line options.
--
-- If type checking completes without any exceptions having been
-- encountered then the command @cmd r@ is executed, where @r@ is the
-- result of 'Imp.typeCheckMain'.

cmd_load'
  :: FilePath  -- ^ File to load into interaction.
  -> [String]  -- ^ Arguments to Agda for loading this file
  -> Bool      -- ^ Allow unsolved meta-variables?
  -> Mode      -- ^ Full type-checking, or only scope-checking?
  -> (CheckResult -> CommandM a)
               -- ^ Continuation after successful loading.
  -> CommandM a
cmd_load' file argv unsolvedOK mode cmd = do

    -- Forget the previous "current file" and interaction points.
    modify $ \ st -> st { theInteractionPoints = []
                        , theCurrentFile       = Nothing
                        }

    -- Update the status. Because the "current file" is not set the
    -- status is not "Checked".
    displayStatus

    -- Reset the state, preserving options and decoded modules. Note
    -- that if the include directories have changed, then the decoded
    -- modules are reset by TCM.setCommandLineOptions' below.
    lift resetState

    -- Clear the info buffer to make room for information about which
    -- module is currently being type-checked.
    putResponse Resp_ClearRunningInfo

    -- Remove any prior syntax highlighting.
    putResponse (Resp_ClearHighlighting NotOnlyTokenBased)

    -- Parse the file.
    --
    -- Note that options are set below.
    fp  <- liftIO $ absolute file
    src <- lift $ Imp.parseSource (SourceFile fp)
    -- Andreas, 2024-08-03, see test/interaction/FileNotFound:
    -- Run 'getModificationTime' after 'parseSource',
    -- otherwise the user gets a weird error for non-existing files.
    -- (We assume that parsing is fast in comparison to type-checking,
    -- so it should not matter much whether we get the time stamp
    -- before or after parsing.)
    t   <- liftIO $ getModificationTime file

    -- Store the warnings.
    warnings <- useTC stTCWarnings

    -- All options are reset when a file is reloaded, including the
    -- choice of whether or not to display implicit arguments.
    opts0 <- gets optionsOnReload
    backends <- useTC stBackends
    let (z, warns) = runOptM $ parseBackendOptions backends argv opts0
    mapM_ (lift . warning . OptionWarning) warns
    case z of
      Left err -> lift $ typeError $ OptionError err
      Right (_, opts) -> do
        opts <- lift $ addTrustedExecutables opts
        let update = over (lensOptAllowUnsolved . lensKeepDefault) (unsolvedOK &&)
            root   = projectRoot fp $ Imp.srcModuleName src
        lift $ TCM.setCommandLineOptions' root $ mapPragmaOptions update opts

    -- Restore the warnings that were saved above.
    modifyTCLens stTCWarnings $ Set.union warnings

    ok <- lift $ Imp.typeCheckMain mode src

    -- The module type checked. If the file was not changed while the
    -- type checker was running then the interaction points and the
    -- "current file" are stored.
    t' <- liftIO $ getModificationTime file
    when (t == t') $ do
      is <- lift $ sortInteractionPoints =<< getInteractionPoints
      modify $ \st -> st { theInteractionPoints = is
                         , theCurrentFile       = Just $ CurrentFile
                             { currentFilePath   = fp
                             , currentFileModule = Imp.srcModuleName src
                             , currentFileArgs   = argv
                             , currentFileStamp  = t
                             }
                         }

    cmd ok

-- | Set 'envCurrentPath' to 'theCurrentFile', if any.
withCurrentFile :: CommandM a -> CommandM a
withCurrentFile m = do
  mfile <- gets $ fmap currentFilePath . theCurrentFile
  localTC (\ e -> e { envCurrentPath = mfile }) m

atTopLevel :: CommandM a -> CommandM a
atTopLevel cmd = liftCommandMT B.atTopLevel cmd

---------------------------------------------------------------------------
-- Giving, refining.

data GiveRefine = Give | Refine | Intro | ElaborateGive Rewrite
  deriving (Eq, Show)

-- | A "give"-like action (give, refine, etc).
--
--   @give_gen force ii rng s give_ref mk_newtxt@
--   acts on interaction point @ii@
--   occupying range @rng@,
--   placing the new content given by string @s@,
--   and replacing @ii@ by the newly created interaction points
--   in the state if safety checks pass (unless @force@ is applied).
give_gen
  :: UseForce       -- ^ Should safety checks be skipped?
  -> InteractionId
  -> Range
  -> String
  -> GiveRefine
  -> CommandM ()
give_gen force ii rng s0 giveRefine = do
  let s = trim s0
  reportSLn "interaction.give" 20 $ "give_gen  " ++ s
  -- Andreas, 2015-02-26 if string is empty do nothing rather
  -- than giving a parse error.
  unless (null s) $ do
    let give_ref =
          case giveRefine of
            Give               -> B.give
            Refine             -> B.refine
            Intro              -> B.refine
            ElaborateGive norm -> B.elaborate_give norm
    -- save scope of the interaction point (for printing the given expr. later)
    scope     <- getInteractionScope ii
    -- parse string and "give", obtaining an abstract expression
    -- and newly created interaction points
    (time, (ae, ae0, iis)) <- maybeTimed $ do
        -- Issue 3000: mark the current hole as solved before giving, to avoid confusing it with potential
        -- new interaction points introduced by the give.
        removeInteractionPoint ii
        mis  <- getInteractionPoints
        reportSLn "interaction.give" 30 $ "interaction points before = " ++ show mis
        given <- lift $ B.parseExprIn ii rng s
        ae    <- lift $ give_ref force ii Nothing given
        mis' <- getInteractionPoints
        reportSLn "interaction.give" 30 $ "interaction points after = " ++ show mis'
        return (ae, given, mis' List.\\ mis)
    -- favonia: backup the old scope for highlighting
    insertOldInteractionScope ii scope
    -- sort the new interaction points and put them into the state
    -- in replacement of the old interaction point
    iis' <- sortInteractionPoints iis
    modifyTheInteractionPoints $ replace ii iis'
    -- print abstract expr
    ce        <- abstractToConcreteScope scope ae
    reportS "interaction.give" 30
      [ "ce = " ++ show ce
      , "scopePrecedence = " ++ show (scope ^. scopePrecedence)
      ]

    -- Issue 7218: if the give/refine command creates an extended
    -- lambda, it also needs to be added to the relevant unfolding sets.
    -- The easiest way to make sure this is consistent is to just re-run
    -- the saturation procedures.
    saturateOpaqueBlocks

    -- if the command was @Give@, use the literal user input;
    -- Andreas, 2014-01-15, see issue 1020:
    -- Refine could solve a goal by introducing the sole constructor
    -- without arguments.  Then there are no interaction metas, but
    -- we still cannot just `give' the user string (which may be empty).
    -- WRONG: also, if no interaction metas were created by @Refine@
    -- WRONG: let literally = (giveRefine == Give || null iis) && rng /= noRange
    -- Ulf, 2015-03-30, if we're doing intro we can't do literal give since
    -- there is nothing in the hole (issue 1892).
    let literally = (giveRefine == Give || giveRefine == Refine) && ae == ae0 && rng /= noRange
    -- Ulf, 2014-01-24: This works for give since we're highlighting the string
    -- that's already in the buffer. Doing it before the give action means that
    -- the highlighting is moved together with the text when the hole goes away.
    -- To make it work for refine we'd have to adjust the ranges.
    when literally $ do
      l <- asksTC envHighlightingLevel
      when (l /= None) $ lift $ do
        printHighlightingInfo KeepHighlighting =<<
          generateTokenInfoFromString rng s
        highlightExpr ae
    putResponse $ Resp_GiveAction ii $ mkNewTxt literally ce
    reportSLn "interaction.give" 30 $ "putResponse GiveAction passed"
    -- display new goal set (if not measuring time)
    maybe (interpret $ Cmd_metas AsIs) (display_info . Info_Time) time
    reportSLn "interaction.give" 30 $ "interpret Cmd_metas passed"
  where
    -- Substitutes xs for x in ys.
    replace x xs ys = concatMap (\ y -> if y == x then xs else [y]) ys
    -- For @Give@ we can replace the ii by the user given input.
    mkNewTxt True  C.Paren{} = Give_Paren
    mkNewTxt True  _         = Give_NoParen
    -- Otherwise, we replace it by the reified value Agda computed.
    mkNewTxt False ce        = Give_String $ prettyShow ce

highlightExpr :: A.Expr -> TCM ()
highlightExpr e =
  localTC (\st -> st { envImportPath         = []
                     , envHighlightingLevel  = NonInteractive
                     , envHighlightingMethod = Direct }) $
    generateAndPrintSyntaxInfo decl Full True
  where
    dummy = mkName_ (NameId 0 noModuleNameHash) ("dummy" :: String)
    info  = mkDefInfo (nameConcrete dummy) noFixity' PublicAccess ConcreteDef (getRange e)
    decl  = A.Axiom OtherDefName info defaultArgInfo Nothing (qnameFromList $ singleton dummy) e

-- | Sorts interaction points based on their ranges.

sortInteractionPoints
  :: (MonadInteractionPoints m, MonadError TCErr m, MonadDebug m)
  => [InteractionId] -> m [InteractionId]
sortInteractionPoints is =
  map fst . List.sortBy (compare `on` snd) <$> do
    forM is $ \ i -> do
      (i,) <$> getInteractionRange i

-- | Displays the current goal, the given document, and the current
--   context.
--
--   Should not modify the state.

cmd_goal_type_context_and :: GoalTypeAux -> Rewrite -> InteractionId -> Range ->
                             String -> CommandM ()
cmd_goal_type_context_and aux norm ii _ _ = do
  ctx <- lift $ B.getResponseContext norm ii
  constr <- lift $ lookupInteractionId ii >>= B.getConstraintsMentioning norm
  boundary <- lift $ B.getIPBoundary norm ii
  display_info $ Info_GoalSpecific ii (Goal_GoalType norm aux ctx boundary constr)

-- | Shows all the top-level names in the given module, along with
-- their types.

showModuleContents :: Rewrite -> Range -> String -> CommandM ()
showModuleContents norm rng s = do
  (modules, tel, types) <- lift $ B.moduleContents norm rng s
  display_info $ Info_ModuleContents modules tel types

-- | Shows all the top-level names in scope which mention all the given
-- identifiers in their type.

searchAbout :: Rewrite -> Range -> String -> CommandM ()
searchAbout norm rg names = do
  unlessNull (trim names) $ \ trimmedNames -> do
    hits <- lift $ findMentions norm rg trimmedNames
    display_info $ Info_SearchAbout hits trimmedNames

-- | Explain why something is in scope.

whyInScope :: String -> CommandM ()
whyInScope s = do
  Just file <- gets theCurrentFile
  let cwd = takeDirectory (filePath $ currentFilePath file)
  why <- liftLocalState $ B.whyInScope cwd s
  display_info $ Info_WhyInScope why

-- | Sets the command line options and updates the status information.

setCommandLineOpts :: CommandLineOptions -> CommandM ()
setCommandLineOpts opts = do
    lift $ TCM.setCommandLineOptions opts
    displayStatus


-- | Computes some status information.
--
--   Does not change the state.

status :: CommandM Status
status = do
  cf       <- gets theCurrentFile
  showImpl <- lift showImplicitArguments
  showIrr  <- lift showIrrelevantArguments

  -- Check if the file was successfully type checked, and has not
  -- changed since. Note: This code does not check if any dependencies
  -- have changed, and uses a time stamp to check for changes.
  checked  <- lift $ case cf of
    Nothing -> return False
    Just f  -> do
      t <- liftIO $ getModificationTime $ filePath (currentFilePath f)
      if currentFileStamp f == t
        then
          maybe False (null . miWarnings) <$>
          getVisitedModule (currentFileModule f)
        else
            return False

  return $ Status { sShowImplicitArguments   = showImpl,
                    sShowIrrelevantArguments = showIrr,
                    sChecked                 = checked }

-- | Displays or updates status information.
--
--   Does not change the state.

displayStatus :: CommandM ()
displayStatus =
  putResponse . Resp_Status  =<< status

-- | @display_info@ does what @'display_info'' False@ does, but
--   additionally displays some status information (see 'status' and
--   'displayStatus').

display_info :: DisplayInfo -> CommandM ()
display_info info = do
  displayStatus
  putResponse $ Resp_DisplayInfo info

-- | Parses and scope checks an expression (using the \"inside scope\"
-- as the scope), performs the given command with the expression as
-- input, and returns the result and the time it takes.

parseAndDoAtToplevel
  :: (A.Expr -> TCM a)
     -- ^ The command to perform.
  -> String
     -- ^ The expression to parse.
  -> CommandM (Maybe CPUTime, a)
parseAndDoAtToplevel cmd s = do
  localStateCommandM $ do
    (e, attrs) <- lift $ runPM $ parse exprParser s
    lift $ checkAttributes attrs
    maybeTimed $ atTopLevel $ lift $
      cmd =<< concreteToAbstract_ e

maybeTimed :: CommandM a -> CommandM (Maybe CPUTime, a)
maybeTimed work = do
  doTime <- lift $ hasProfileOption Profile.Interactive
  if not doTime
    then (Nothing,) <$> work
    else do
      (r, time) <- measureTime work
      return (Just time, r)

-- | Tell to highlight the code using the given highlighting
-- info (unless it is @Nothing@).

tellToUpdateHighlighting
  :: Maybe (HighlightingInfo, HighlightingMethod, ModuleToSource) -> IO [Response]
tellToUpdateHighlighting Nothing                = return []
tellToUpdateHighlighting (Just (info, method, modFile)) =
  return [Resp_HighlightingInfo info KeepHighlighting method modFile]

-- | Tells the Emacs mode to go to the first error position (if any).

tellEmacsToJumpToError :: Range -> [Response]
tellEmacsToJumpToError r =
  case rStart r of
    Nothing                                           -> []
    Just (Pn { srcFile = Strict.Nothing })            -> []
    Just (Pn { srcFile = Strict.Just f, posPos = p }) ->
       [ Resp_JumpToError (filePath (rangeFilePath f)) p ]
