{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -fno-cse #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Interaction.InteractionTop
  ( module Agda.Interaction.InteractionTop
  )
  where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Concurrent
import Control.Concurrent.Async
import Control.Concurrent.STM.TChan
import qualified Control.Exception as E
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.STM

import qualified Data.Char as Char
import Data.Foldable (Foldable)
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Traversable as Trav

import System.Directory
import System.FilePath

import Agda.TypeChecking.Monad as TM
  hiding (initState, setCommandLineOptions)
import qualified Agda.TypeChecking.Monad as TM
import qualified Agda.TypeChecking.Pretty as TCP
import Agda.TypeChecking.Errors

import Agda.Syntax.Fixity
import Agda.Syntax.Position
import Agda.Syntax.Parser
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Generic as C
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Info (mkDefInfo)
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete hiding (withScope)
import Agda.Syntax.Scope.Base

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Options.Lenses as Lenses
import Agda.Interaction.MakeCase
import Agda.Interaction.SearchAbout
import Agda.Interaction.Response hiding (Function, ExtendedLambda)
import qualified Agda.Interaction.Response as R
import qualified Agda.Interaction.BasicOps as B
import Agda.Interaction.BasicOps hiding (whyInScope)
import Agda.Interaction.Highlighting.Precise hiding (Postulate)
import qualified Agda.Interaction.Imports as Imp
import Agda.Interaction.Highlighting.Generate
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import qualified Agda.Interaction.Highlighting.Range as H

import Agda.Compiler.Common (IsMain (..))
import Agda.Compiler.Backend

import Agda.Auto.Auto as Auto

import Agda.Utils.Except
  ( ExceptT
  , mkExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )

import Agda.Utils.FileName
import Agda.Utils.Function
import Agda.Utils.Hash
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Lens
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.String
import Agda.Utils.Time

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- The CommandM monad

-- | Auxiliary state of an interactive computation.

data CommandState = CommandState
  { theInteractionPoints :: [InteractionId]
    -- ^ The interaction points of the buffer, in the order in which
    --   they appear in the buffer. The interaction points are
    --   recorded in 'theTCState', but when new interaction points are
    --   added by give or refine Agda does not ensure that the ranges
    --   of later interaction points are updated.
  , theCurrentFile       :: Maybe (AbsolutePath, ClockTime)
    -- ^ The file which the state applies to. Only stored if the
    -- module was successfully type checked (potentially with
    -- warnings). The 'ClockTime' is the modification time stamp of
    -- the file when it was last loaded.
  , optionsOnReload :: CommandLineOptions
    -- ^ Reset the options on each reload to these.
  , oldInteractionScopes :: !OldInteractionScopes
    -- ^ We remember (the scope of) old interaction points to make it
    --   possible to parse and compute highlighting information for the
    --   expression that it got replaced by.
  , commandQueue :: CommandQueue
    -- ^ Command queue.
    --
    -- The commands in the queue are processed in the order in which
    -- they are received. Abort commands do not have precedence over
    -- other commands, they only abort the immediately preceding
    -- command. (The Emacs mode is expected not to send a new command,
    -- other than the abort command, before the previous command has
    -- completed.)
  }

type OldInteractionScopes = Map InteractionId ScopeInfo

-- | Initial auxiliary interaction state

initCommandState :: CommandQueue -> CommandState
initCommandState commandQueue =
  CommandState
    { theInteractionPoints = []
    , theCurrentFile       = Nothing
    , optionsOnReload      = defaultOptions
    , oldInteractionScopes = Map.empty
    , commandQueue         = commandQueue
    }

-- | Monad for computing answers to interactive commands.
--
--   'CommandM' is 'TCM' extended with state 'CommandState'.

type CommandM = StateT CommandState TCM

-- | Restore both 'TCState' and 'CommandState'.

localStateCommandM :: CommandM a -> CommandM a
localStateCommandM m = do
  cSt <- get
  tcSt <- lift $ get
  x <- m
  lift $ put tcSt
  put cSt
  return x

-- | Restore 'TCState', do not touch 'CommandState'.

liftLocalState :: TCM a -> CommandM a
liftLocalState = lift . localState

-- | Build an opposite action to 'lift' for state monads.

revLift
    :: MonadState st m
    => (forall c . m c -> st -> k (c, st))      -- ^ run
    -> (forall b . k b -> m b)                  -- ^ lift
    -> (forall x . (m a -> k x) -> k x) -> m a  -- ^ reverse lift in double negative position
revLift run lift f = do
    st <- get
    (a, st) <- lift $ f (`run` st)
    put st
    return a

-- | Opposite of 'liftIO' for 'CommandM'.
--   Use only if main errors are already catched.

commandMToIO :: (forall x . (CommandM a -> IO x) -> IO x) -> CommandM a
commandMToIO ci_i = revLift runStateT lift $ \ct -> revLift runSafeTCM liftIO $ ci_i . (. ct)

-- | Lift a TCM action transformer to a CommandM action transformer.

liftCommandMT :: (forall a . TCM a -> TCM a) -> CommandM a -> CommandM a
liftCommandMT f m = revLift runStateT lift $ f . ($ m)

-- | Ditto, but restore state.

liftCommandMTLocalState :: (forall a . TCM a -> TCM a) -> CommandM a -> CommandM a
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
    Nothing    -> fail $ "not an old interaction point: " ++ show ii
    Just scope -> return scope

-- | Do setup and error handling for a command.

handleCommand_ :: CommandM () -> CommandM ()
handleCommand_ = handleCommand id (return ())

handleCommand :: (forall a. CommandM a -> CommandM a) -> CommandM () -> CommandM () -> CommandM ()
handleCommand wrap onFail cmd = handleNastyErrors $ wrap $ do
    oldState <- lift get

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
      handleErr e
      -- Andreas, 2016-11-18, issue #2174
      -- Reset TCState after error is handled, to get rid of metas created during failed command
      lift $ do
        newPersistentState <- use lensPersistentState
        put oldState
        lensPersistentState .= newPersistentState

  where
    -- Preserves state so we can do unsolved meta highlighting
    catchErr :: CommandM a -> (TCErr -> CommandM a) -> CommandM a
    catchErr m h = do
      s       <- get
      (x, s') <- lift $ do disableDestructiveUpdate (runStateT m s)
         `catchError_` \ e ->
           runStateT (h e) s
      put s'
      return x

    -- | Handle every possible kind of error (#637), except for
    -- ThreadKilled, which is used to abort Agda.
    handleNastyErrors :: CommandM () -> CommandM ()
    handleNastyErrors m = commandMToIO $ \ toIO -> do
      let handle e =
            Right <$>
              (toIO $ handleErr $ Exception noRange $ text $ show e)

          asyncHandler e@E.ThreadKilled = return (Left e)
          asyncHandler e                = handle e

          generalHandler (e :: E.SomeException) = handle e

      r <- ((Right <$> toIO m) `E.catch` asyncHandler)
             `E.catch` generalHandler
      case r of
        Right x -> return x
        Left e  -> E.throwIO e

    -- | Displays an error and instructs Emacs to jump to the site of the
    -- error. Because this function may switch the focus to another file
    -- the status information is also updated.
    handleErr e = do
        unsolvedNotOK <- lift $ not . optAllowUnsolved <$> pragmaOptions
        meta    <- lift $ computeUnsolvedMetaWarnings
        constr  <- lift $ computeUnsolvedConstraints
        err     <- lift $ errorHighlighting e
        modFile <- lift $ use stModuleToSource
        method  <- lift $ view eHighlightingMethod
        let info = compress $ mconcat $
                     -- Errors take precedence over unsolved things.
                     err : if unsolvedNotOK then [meta, constr] else []
        s1 <- lift $ prettyError e
        s2 <- lift $ prettyTCWarnings' =<< Imp.errorWarningsOfTCErr e
        let s = List.intercalate "\n" $ filter (not . null) $ s1 : s2
        x <- lift $ optShowImplicit <$> use stPragmaOptions
        unless (null s1) $ mapM_ putResponse $
            [ Resp_DisplayInfo $ Info_Error s ] ++
            tellEmacsToJumpToError (getRange e) ++
            [ Resp_HighlightingInfo info method modFile ] ++
            [ Resp_Status $ Status { sChecked = False
                                   , sShowImplicitArguments = x
                                   } ]

-- | Run an 'IOTCM' value, catch the exceptions, emit output
--
--   If an error happens the state of 'CommandM' does not change,
--   but stPersistent may change (which contains successfully
--   loaded interfaces for example).

runInteraction :: IOTCM -> CommandM ()
runInteraction (IOTCM current highlighting highlightingMethod cmd) =
  handleCommand inEmacs onFail $ do
    current <- liftIO $ absolute current
    -- Raises an error if the given file is not the one currently
    -- loaded.
    cf <- gets theCurrentFile
    when (not (independent cmd) && Just current /= (fst <$> cf)) $
        lift $ typeError $ GenericError "Error: First load the file."

    withCurrentFile $ interpret cmd

    cf <- gets theCurrentFile
    when (Just current == (fst <$> cf)) $
        putResponse . Resp_InteractionPoints =<< gets theInteractionPoints

  where
    inEmacs = liftCommandMT $ withEnv $ initEnv
            { envHighlightingLevel  = highlighting
            , envHighlightingMethod = highlightingMethod
            }

    -- If an independent command fails we should reset theCurrentFile (Issue853).
    onFail | independent cmd = modify $ \ s -> s { theCurrentFile = Nothing }
           | otherwise       = return ()

------------------------------------------------------------------------
-- Command queues

-- | Commands.

data Command
  = Command IOTCM
    -- ^ An 'IOTCM' command.
  | Done
    -- ^ Stop processing commands.
  | Error String
    -- ^ An error message for a command that could not be parsed.
  deriving Show

-- | Command queues.

type CommandQueue = TChan Command

-- | The next command.

nextCommand :: CommandM Command
nextCommand =
  liftIO . atomically . readTChan =<< gets commandQueue

-- | Runs the given computation, but if an abort command is
-- encountered (and acted upon), then the computation is interrupted,
-- the persistent state and all options are restored, and some
-- commands are sent to the frontend.

-- TODO: It might be nice if some of the changes to the persistent
-- state inflicted by the interrupted computation were preserved.

maybeAbort :: CommandM () -> CommandM ()
maybeAbort c = do
  commandState <- get
  tcState      <- lift get
  tcEnv        <- lift ask
  result       <- liftIO $ race
                    (runTCM tcEnv tcState $ runStateT c commandState)
                    (waitForAbort $ commandQueue commandState)
  case result of
    Left (((), commandState), tcState) -> do
      lift $ put tcState
      put commandState
    Right () -> do
      lift $ put $ initState
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
  where

  -- | Returns if the first element in the queue is an abort command.
  -- The abort command is removed from the queue.

  waitForAbort :: CommandQueue -> IO ()
  waitForAbort q = atomically $ do
    c <- peekTChan q
    case c of
      Command (IOTCM _ _ _ Cmd_abort) -> void $ readTChan q
      _                               -> retry

-- | Creates a command queue, and forks a thread that writes commands
-- to the queue. The queue is returned.

initialiseCommandQueue
  :: IO Command
     -- ^ Returns the next command.
  -> IO CommandQueue
initialiseCommandQueue next = do
  q <- newTChanIO
  let readCommands = do
        c <- next
        atomically $ writeTChan q c
        case c of
          Done -> return ()
          _    -> readCommands
  _ <- forkIO readCommands
  return q

----------------------------------------------------------------------------
-- | An interactive computation.

type Interaction = Interaction' Range

data Interaction' range
    -- | @cmd_load m argv@ loads the module in file @m@, using
    -- @argv@ as the command-line options.
  = Cmd_load            FilePath [String]

    -- | @cmd_compile b m argv@ compiles the module in file @m@ using
    -- the backend @b@, using @argv@ as the command-line options.
  | Cmd_compile         CompilerBackend FilePath [String]

  | Cmd_constraints

    -- | Show unsolved metas. If there are no unsolved metas but unsolved constraints
    -- show those instead.
  | Cmd_metas

    -- | Display all warnings.
  | Cmd_warnings

    -- | Shows all the top-level names in the given module, along with
    -- their types. Uses the top-level scope.
  | Cmd_show_module_contents_toplevel
                        B.Rewrite
                        String

    -- | Shows all the top-level names in scope which mention all the given
    -- identifiers in their type.
  | Cmd_search_about_toplevel B.Rewrite String

    -- | Solve (all goals / the goal at point) whose values are determined by
    -- the constraints.
  | Cmd_solveAll B.Rewrite
  | Cmd_solveOne B.Rewrite InteractionId range String

    -- | Parse the given expression (as if it were defined at the
    -- top-level of the current module) and infer its type.
  | Cmd_infer_toplevel  B.Rewrite  -- Normalise the type?
                        String


    -- | Parse and type check the given expression (as if it were defined
    -- at the top-level of the current module) and normalise it.
  | Cmd_compute_toplevel B.ComputeMode
                         String

    ------------------------------------------------------------------------
    -- Syntax highlighting

    -- | @cmd_load_highlighting_info source@ loads syntax highlighting
    -- information for the module in @source@, and asks Emacs to apply
    -- highlighting info from this file.
    --
    -- If the module does not exist, or its module name is malformed or
    -- cannot be determined, or the module has not already been visited,
    -- or the cached info is out of date, then no highlighting information
    -- is printed.
    --
    -- This command is used to load syntax highlighting information when a
    -- new file is opened, and it would probably be annoying if jumping to
    -- the definition of an identifier reset the proof state, so this
    -- command tries not to do that. One result of this is that the
    -- command uses the current include directories, whatever they happen
    -- to be.
  | Cmd_load_highlighting_info
                        FilePath

    -- | Tells Agda to compute highlighting information for the expression just
    --   spliced into an interaction point.
  | Cmd_highlight InteractionId range String

    ------------------------------------------------------------------------
    -- Implicit arguments

    -- | Tells Agda whether or not to show implicit arguments.
  | ShowImplicitArgs    Bool -- Show them?


    -- | Toggle display of implicit arguments.
  | ToggleImplicitArgs

    ------------------------------------------------------------------------
    -- | Goal commands
    --
    -- If the range is 'noRange', then the string comes from the
    -- minibuffer rather than the goal.

  | Cmd_give            InteractionId range String

  | Cmd_refine          InteractionId range String

  | Cmd_intro           Bool InteractionId range String

  | Cmd_refine_or_intro Bool InteractionId range String

  | Cmd_auto            InteractionId range String

  | Cmd_context         B.Rewrite InteractionId range String

  | Cmd_helper_function B.Rewrite InteractionId range String

  | Cmd_infer           B.Rewrite InteractionId range String

  | Cmd_goal_type       B.Rewrite InteractionId range String

    -- | Displays the current goal and context.
  | Cmd_goal_type_context B.Rewrite InteractionId range String

    -- | Displays the current goal and context /and/ infers the type of an
    -- expression.
  | Cmd_goal_type_context_infer
                        B.Rewrite InteractionId range String

    -- | Shows all the top-level names in the given module, along with
    -- their types. Uses the scope of the given goal.
  | Cmd_show_module_contents
                        B.Rewrite InteractionId range String

  | Cmd_make_case       InteractionId range String

  | Cmd_compute         B.ComputeMode
                        InteractionId range String

  | Cmd_why_in_scope    InteractionId range String
  | Cmd_why_in_scope_toplevel String
    -- | Displays version of the running Agda
  | Cmd_show_version
  | Cmd_abort
    -- ^ Abort the current computation.
    --
    -- Does nothing if no computation is in progress.
        deriving (Show, Read, Functor, Foldable, Traversable)

type IOTCM = IOTCM' Range
data IOTCM' range
    = IOTCM
        FilePath
         -- -^ The current file. If this file does not match
         -- 'theCurrentFile, and the 'Interaction' is not
         -- \"independent\", then an error is raised.
        HighlightingLevel
        HighlightingMethod
        (Interaction' range)
         -- -^ What to do
            deriving (Show, Read, Functor, Foldable, Traversable)

---------------------------------------------------------
-- Read instances


-- | The 'Parse' monad.
--   'StateT' state holds the remaining input.

type Parse a = ExceptT String (StateT String Identity) a

-- | Converter from the type of 'reads' to 'Parse'
--   The first paramter is part of the error message
--   in case the parse fails.

readsToParse :: String -> (String -> Maybe (a, String)) -> Parse a
readsToParse s f = do
    st <- lift get
    case f st of
        Nothing -> throwError s
        Just (a, st) -> do
            lift $ put st
            return a

parseToReadsPrec :: Parse a -> Int -> String -> [(a, String)]
parseToReadsPrec p i s = case runIdentity . flip runStateT s . runExceptT $ parens' p of
    (Right a, s) -> [(a,s)]
    _ -> []

-- | Demand an exact string.

exact :: String -> Parse ()
exact s = readsToParse (show s) $ fmap (\x -> ((),x)) . List.stripPrefix s . dropWhile (==' ')

readParse :: Read a => Parse a
readParse = readsToParse "read failed" $ listToMaybe . reads

parens' :: Parse a -> Parse a
parens' p = do
    exact "("
    x <- p
    exact ")"
    return x
  `mplus`
    p

instance Read InteractionId where
    readsPrec = parseToReadsPrec $
        fmap InteractionId readParse

-- | Note that the grammar implemented by this instance does not
-- necessarily match the current representation of ranges.

instance Read a => Read (Range' a) where
    readsPrec = parseToReadsPrec $
      (exact "intervalsToRange" >>
       liftM2 intervalsToRange readParse readParse)
        `mplus`
      (exact "noRange" >> return noRange)

instance Read a => Read (Interval' a) where
    readsPrec = parseToReadsPrec $ do
        exact "Interval"
        liftM2 Interval readParse readParse

instance Read AbsolutePath where
    readsPrec = parseToReadsPrec $ do
        exact "mkAbsolute"
        fmap mkAbsolute readParse

instance Read a => Read (Position' a) where
    readsPrec = parseToReadsPrec $ do
        exact "Pn"
        liftM4 Pn readParse readParse readParse readParse

---------------------------------------------------------

-- | Can the command run even if the relevant file has not been loaded
--   into the state?

independent :: Interaction -> Bool
independent (Cmd_load {})                   = True
independent (Cmd_compile {})                = True
independent (Cmd_load_highlighting_info {}) = True
independent Cmd_show_version                = True
independent _                               = False

-- | Interpret an interaction

interpret :: Interaction -> CommandM ()

interpret (Cmd_load m argv) =
  cmd_load' m argv True Imp.TypeCheck $ \_ -> interpret Cmd_metas

interpret (Cmd_compile b file argv) =
  cmd_load' file argv (b `elem` [LaTeX, QuickLaTeX])
            (if b == QuickLaTeX
             then Imp.ScopeCheck
             else Imp.TypeCheck) $ \(i, mw) -> do
    mw <- lift $ Imp.applyFlagsToMaybeWarnings RespectFlags mw
    case mw of
      Imp.NoWarnings -> do
        lift $ case b of
          LaTeX                    -> LaTeX.generateLaTeX i
          QuickLaTeX               -> LaTeX.generateLaTeX i
          OtherBackend "GHCNoMain" -> callBackend "GHC" NotMain i   -- for backwards compatibility
          OtherBackend b           -> callBackend b IsMain  i
        (pwe, pwa) <- interpretWarnings
        display_info $ Info_CompilationOk pwa pwe
      Imp.SomeWarnings w -> do
        pw <- lift $ prettyTCWarnings w
        display_info $ Info_Error $ unlines
          [ "You need to fix the following errors before you can compile"
          , "the module:"
          , ""
          , pw
          ]

interpret Cmd_constraints =
    display_info . Info_Constraints . unlines . map show =<< lift B.getConstraints

interpret Cmd_metas = do -- CL.showMetas []
  unsolvedNotOK <- lift $ not . optAllowUnsolved <$> pragmaOptions
  ms <- lift showOpenMetas
  (pwe, pwa) <- interpretWarnings
  display_info $ Info_AllGoalsWarnings (unlines ms) pwa pwe

interpret Cmd_warnings = do
  -- Ulf, 2016-08-09: Warnings are now printed in the info buffer by Cmd_metas.
  -- pws <- interpretWarnings
  -- unless (null pwd) $ display_info $ Info_Warning pws
  return ()


interpret (Cmd_show_module_contents_toplevel norm s) =
  liftCommandMT B.atTopLevel $ showModuleContents norm noRange s

interpret (Cmd_search_about_toplevel norm s) =
  liftCommandMT B.atTopLevel $ searchAbout norm noRange s

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

interpret (Cmd_infer_toplevel norm s) =
  parseAndDoAtToplevel (B.typeInCurrent norm) Info_InferredType s

interpret (Cmd_compute_toplevel cmode s) =
  parseAndDoAtToplevel' action Info_NormalForm $ computeWrapInput cmode s
  where
  action = allowNonTerminatingReductions
         . (if computeIgnoreAbstract cmode then ignoreAbstractMode else inConcreteMode)
         . (B.showComputed cmode <=< B.evalInCurrent)


interpret (ShowImplicitArgs showImpl) = do
  opts <- lift commandLineOptions
  setCommandLineOpts $
    opts { optPragmaOptions =
             (optPragmaOptions opts) { optShowImplicit = showImpl } }

interpret ToggleImplicitArgs = do
  opts <- lift commandLineOptions
  let ps = optPragmaOptions opts
  setCommandLineOpts $
    opts { optPragmaOptions =
             ps { optShowImplicit = not $ optShowImplicit ps } }

interpret (Cmd_load_highlighting_info source) = do
    -- Make sure that the include directories have
    -- been set.
    setCommandLineOpts =<< lift commandLineOptions

    resp <- lift $ liftIO . tellToUpdateHighlighting =<< do
      ex <- liftIO $ doesFileExist source
      absSource <- liftIO $ absolute source
      case ex of
        False -> return Nothing
        True  -> do
          mmi <- (getVisitedModule =<<
                    moduleName absSource)
                   `catchError`
                 \_ -> return Nothing
          case mmi of
            Nothing -> return Nothing
            Just mi -> do
              sourceH <- liftIO $ hashFile absSource
              if sourceH == iSourceHash (miInterface mi)
               then do
                modFile <- use stModuleToSource
                method  <- view eHighlightingMethod
                return $ Just (iHighlighting $ miInterface mi, method, modFile)
               else
                return Nothing
    mapM_ putResponse resp

interpret (Cmd_highlight ii rng s) = do
  scope <- getOldInteractionScope ii
  removeOldInteractionScope ii
  handle $ do
    e <- try ("Highlighting failed to parse expression in " ++ show ii) $
           B.parseExpr rng s
    e <- try ("Highlighting failed to scope check expression in " ++ show ii) $
           concreteToAbstract scope e
    lift $ printHighlightingInfo =<< generateTokenInfoFromString rng s
    lift $ highlightExpr e
  where
    handle :: ExceptT String TCM () -> CommandM ()
    handle m = do
      res <- lift $ runExceptT m
      case res of
        Left s  -> display_info $ Info_Error s
        Right _ -> return ()
    try :: String -> TCM a -> ExceptT String TCM a
    try err m = mkExceptT $ do
      (Right <$> m) `catchError` \ _ -> return (Left err)

interpret (Cmd_give   ii rng s) = give_gen ii rng s Give
interpret (Cmd_refine ii rng s) = give_gen ii rng s Refine

interpret (Cmd_intro pmLambda ii rng _) = do
  ss <- lift $ B.introTactic pmLambda ii
  liftCommandMT (B.withInteractionId ii) $ case ss of
    []    -> do
      display_info $ Info_Intro $ text "No introduction forms found."
    [s]   -> give_gen ii rng s Intro
    _:_:_ -> do
      display_info $ Info_Intro $
        sep [ text "Don't know which constructor to introduce of"
            , let mkOr []     = []
                  mkOr [x, y] = [text x <+> text "or" <+> text y]
                  mkOr (x:xs) = text x : mkOr xs
              in nest 2 $ fsep $ punctuate comma (mkOr ss)
            ]

interpret (Cmd_refine_or_intro pmLambda ii r s) = interpret $
  let s' = trim s
  in (if null s' then Cmd_intro pmLambda else Cmd_refine) ii r s'

interpret (Cmd_auto ii rng s) = do
  -- Andreas, 2014-07-05 Issue 1226:
  -- Save the state to have access to even those interaction ids
  -- that Auto solves (since Auto gives the solution right away).
  st <- lift $ get
  (time , res) <- maybeTimed $ lift $ Auto.auto ii rng s
  case autoProgress res of
   Solutions sols -> do
    lift $ reportSLn "auto" 10 $ "Auto produced the following solutions " ++ show sols
    forM_ sols $ \(ii, s) -> do
      -- Andreas, 2014-07-05 Issue 1226:
      -- For highlighting, Resp_GiveAction needs to access
      -- the @oldInteractionScope@s of the interaction points solved by Auto.
      -- We dig them out from the state before Auto was invoked.
      insertOldInteractionScope ii =<< liftLocalState (put st >> getInteractionScope ii)
      -- Andreas, 2014-07-07: NOT TRUE:
      -- -- Andreas, 2014-07-05: The following should be obsolete,
      -- -- as Auto has removed the interaction points already:
      -- modifyTheInteractionPoints $ filter (/= ii)
      putResponse $ Resp_GiveAction ii $ Give_String s
    -- Andreas, 2014-07-07: Remove the interaction points in one go.
    modifyTheInteractionPoints (List.\\ (map fst sols))
    case autoMessage res of
     Nothing  -> interpret Cmd_metas
     Just msg -> display_info $ Info_Auto msg
   FunClauses cs -> do
    case autoMessage res of
     Nothing  -> return ()
     Just msg -> display_info $ Info_Auto msg
    putResponse $ Resp_MakeCase R.Function cs
   Refinement s -> give_gen ii rng s Refine
  maybe (return ()) (display_info . Info_Time) time

interpret (Cmd_context norm ii _ _) =
  display_info . Info_Context =<< liftLocalState (prettyContext norm False ii)

interpret (Cmd_helper_function norm ii rng s) =
  display_info . Info_HelperFunction =<< liftLocalState (cmd_helper_function norm ii rng s)

interpret (Cmd_infer norm ii rng s) =
  display_info . Info_InferredType
    =<< liftLocalState (B.withInteractionId ii
          (prettyATop =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s))

interpret (Cmd_goal_type norm ii _ _) =
  display_info . Info_CurrentGoal
    =<< liftLocalState (B.withInteractionId ii $ prettyTypeOfMeta norm ii)

interpret (Cmd_goal_type_context norm ii rng s) =
  cmd_goal_type_context_and empty norm ii rng s

interpret (Cmd_goal_type_context_infer norm ii rng s) = do
  -- In case of the empty expression to type, don't fail with
  -- a stupid parse error, but just fall back to
  -- Cmd_goal_type_context.
  have <- if all Char.isSpace s then return empty else liftLocalState $ do
    typ <- B.withInteractionId ii $
      prettyATop =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s
    return $ text "Have:" <+> typ
  cmd_goal_type_context_and have norm ii rng s

interpret (Cmd_show_module_contents norm ii rng s) =
  liftCommandMT (B.withInteractionId ii) $ showModuleContents norm rng s

interpret (Cmd_why_in_scope_toplevel s) =
  liftCommandMT B.atTopLevel $ whyInScope s

interpret (Cmd_why_in_scope ii rng s) =
  liftCommandMT (B.withInteractionId ii) $ whyInScope s

interpret (Cmd_make_case ii rng s) = do
  (f, casectxt, cs) <- lift $ makeCase ii rng s
  liftCommandMT (B.withInteractionId ii) $ do
    hidden <- lift $ showImplicitArguments
    tel <- lift $ lookupSection (qnameModule f) -- don't shadow the names in this telescope
    let cs'  :: [A.Clause] = List.map (extlam_dropLLifted casectxt hidden) cs
    pcs      :: [Doc]     <- lift $ inTopContext $ addContext tel $ mapM prettyA cs'
    let pcs' :: [String]   = List.map (extlam_dropName casectxt . render) pcs
    lift $ reportSDoc "interaction.case" 60 $ TCP.vcat
      [ TCP.text "InteractionTop.Cmd_make_case"
      , TCP.nest 2 $ TCP.vcat
        [ TCP.text "cs   = " TCP.<+> TCP.vcat (map prettyA cs)
        , TCP.text "cs'  = " TCP.<+> TCP.vcat (map prettyA cs')
        , TCP.text "pcs  = " TCP.<+> TCP.vcat (map return pcs)
        , TCP.text "pcs' = " TCP.<+> TCP.vcat (map TCP.text pcs')
        ]
      ]
    lift $ reportSDoc "interaction.case" 90 $ TCP.vcat
      [ TCP.text "InteractionTop.Cmd_make_case"
      , TCP.nest 2 $ TCP.vcat
        [ TCP.text "cs   = " TCP.<+> TCP.text (show cs)
        , TCP.text "cs'  = " TCP.<+> TCP.text (show cs')
        ]
      ]
    putResponse $ Resp_MakeCase (makeCaseVariant casectxt) pcs'
  where
    render = renderStyle (style { mode = OneLineMode })

    makeCaseVariant :: CaseContext -> MakeCaseVariant
    makeCaseVariant Nothing = R.Function
    makeCaseVariant Just{}  = R.ExtendedLambda

    -- very dirty hack, string manipulation by dropping the function name
    -- and replacing the last " = " with " -> ". It's important not to replace
    -- the equal sign in named implicit with an arrow!
    extlam_dropName :: CaseContext -> String -> String
    extlam_dropName Nothing x = x
    extlam_dropName Just{}  x
        = unwords $ reverse $ replEquals $ reverse $ drop 1 $ words x
      where
        replEquals ("=" : ws) = "→" : ws
        replEquals (w   : ws) = w : replEquals ws
        replEquals []         = []

    -- Drops pattern added to extended lambda functions when lambda lifting them
    extlam_dropLLifted :: CaseContext -> Bool -> A.Clause -> A.Clause
    extlam_dropLLifted Nothing _ x = x
    extlam_dropLLifted _ _ (A.Clause (A.LHS _ A.LHSProj{} _) _ _ _ _) = __IMPOSSIBLE__
    extlam_dropLLifted (Just (ExtLamInfo h nh)) hidden (A.Clause (A.LHS info (A.LHSHead name nps) ps) dots rhs decl catchall)
      = let n = if hidden then h + nh else nh
        in
         (A.Clause (A.LHS info (A.LHSHead name (drop n nps)) ps) dots rhs decl catchall)

interpret (Cmd_compute cmode ii rng s) = display_info . Info_NormalForm =<< do
  liftLocalState $ do
    e <- B.parseExprIn ii rng $ computeWrapInput cmode s
    B.withInteractionId ii $ do
      showComputed cmode =<< do applyWhen (computeIgnoreAbstract cmode) ignoreAbstractMode $ B.evalInCurrent e


interpret Cmd_show_version = display_info Info_Version

interpret Cmd_abort = return ()

-- | Show warnings
interpretWarnings :: CommandM (String, String)
interpretWarnings = do
  mws <- lift $ Imp.getAllWarnings AllWarnings RespectFlags
  case filter isNotMeta <$> mws of
    Imp.SomeWarnings ws@(_:_) -> do
      let (we, wa) = classifyWarnings ws
      pwe <- lift $ prettyTCWarnings we
      pwa <- lift $ prettyTCWarnings wa
      return (pwe, pwa)
    _ -> return ("", "")
   where isNotMeta w = case tcWarning w of
                         UnsolvedInteractionMetas{} -> False
                         UnsolvedMetaVariables{}    -> False
                         _                          -> True


-- | Solved goals already instantiated internally
-- The second argument potentially limits it to one specific goal.
solveInstantiatedGoals :: B.Rewrite -> Maybe InteractionId -> CommandM ()
solveInstantiatedGoals norm mii = do
  -- Andreas, 2016-10-23 issue #2280: throw away meta elims.
  out <- lift $ local (\ e -> e { envPrintMetasBare = True }) $ do
    sip <- B.getSolvedInteractionPoints False norm
           -- only solve metas which have a proper instantiation, i.e., not another meta
    maybe id (\ ii -> filter ((ii ==) . fst)) mii <$> mapM prt sip
  putResponse $ Resp_SolveAll out
  where
      prt (i, m, e) = do
        mi <- getMetaInfo <$> lookupMeta m
        e <- withMetaInfo mi $ abstractToConcreteCtx TopCtx e
        return (i, e)


-- | Print open metas nicely.
showOpenMetas :: TCM [String]
showOpenMetas = do
  ims <- B.typesOfVisibleMetas B.AsIs
  di <- forM ims $ \ i ->
    B.withInteractionId (B.outputFormId $ B.OutputForm noRange [] i) $
      showATop i
  -- Show unsolved implicit arguments simplified.
  unsolvedNotOK <- not . optAllowUnsolved <$> pragmaOptions
  hms <- (guard unsolvedNotOK >>) <$> B.typesOfHiddenMetas B.Simplified
  dh <- mapM showA' hms
  return $ di ++ dh
  where
    metaId (B.OfType i _) = i
    metaId (B.JustType i) = i
    metaId (B.JustSort i) = i
    metaId (B.Assign i e) = i
    metaId _ = __IMPOSSIBLE__
    showA' :: B.OutputConstraint A.Expr NamedMeta -> TCM String
    showA' m = do
      let i = nmid $ metaId m
      r <- getMetaRange i
      d <- B.withMetaId i (showATop m)
      return $ d ++ "  [ at " ++ show r ++ " ]"


-- | @cmd_load' file argv unsolvedOk cmd@
--   loads the module in file @file@,
--   using @argv@ as the command-line options.
--
-- If type checking completes without any exceptions having been
-- encountered then the command @cmd r@ is executed, where @r@ is the
-- result of 'Imp.typeCheckMain'.

cmd_load' :: FilePath -> [String]
          -> Bool      -- ^ Allow unsolved meta-variables?
          -> Imp.Mode  -- ^ Full type-checking, or only
                       --   scope-checking?
          -> ((Interface, Imp.MaybeWarnings) -> CommandM ())
          -> CommandM ()
cmd_load' file argv unsolvedOK mode cmd = do
    f <- liftIO $ absolute file
    ex <- liftIO $ doesFileExist $ filePath f
    let relativeTo | ex        = ProjectRoot f
                   | otherwise = CurrentDir

    -- Forget the previous "current file" and interaction points.
    modify $ \st -> st { theInteractionPoints = []
                       , theCurrentFile       = Nothing
                       }

    t <- liftIO $ getModificationTime file

    -- All options are reset when a file is reloaded, including the
    -- choice of whether or not to display implicit arguments.
    opts0 <- gets optionsOnReload
    z <- liftIO $ runOptM $ parseStandardOptions' argv opts0
    case z of
      Left err   -> lift $ typeError $ GenericError err
      Right opts -> do
        let update o = o { optAllowUnsolved = unsolvedOK && optAllowUnsolved o}
        lift $ TM.setCommandLineOptions' relativeTo $ mapPragmaOptions update opts
        displayStatus

    -- Reset the state, preserving options and decoded modules. Note
    -- that if the include directories have changed, then the decoded
    -- modules are reset when cmd_load' is run by ioTCM.
    lift resetState

    -- Clear the info buffer to make room for information about which
    -- module is currently being type-checked.
    putResponse Resp_ClearRunningInfo

    -- Remove any prior syntax highlighting.
    putResponse Resp_ClearHighlighting

    -- We activate the cache only when agda is used interactively
    lift activateLoadedFileCache

    ok <- lift $ Imp.typeCheckMain f mode

    -- The module type checked. If the file was not changed while the
    -- type checker was running then the interaction points and the
    -- "current file" are stored.
    t' <- liftIO $ getModificationTime file
    when (t == t') $ do
      is <- lift $ sortInteractionPoints =<< getInteractionPoints
      modify $ \st -> st { theInteractionPoints = is
                         , theCurrentFile       = Just (f, t)
                         }

    cmd ok

-- | Set 'envCurrentPath' to 'theCurrentFile', if any.
withCurrentFile :: CommandM a -> CommandM a
withCurrentFile m = do
  mfile <- fmap fst <$> gets theCurrentFile
  local (\ e -> e { envCurrentPath = mfile }) m

-- | Available backends.

data CompilerBackend = LaTeX | QuickLaTeX | OtherBackend String
    deriving (Eq)

instance Show CompilerBackend where
  show LaTeX            = "LaTeX"
  show QuickLaTeX       = "QuickLaTeX"
  show (OtherBackend s) = s

instance Read CompilerBackend where
  readsPrec _ s = do
    (t, s) <- lex s
    let b = case t of
              "LaTeX"      -> LaTeX
              "QuickLaTeX" -> QuickLaTeX
              _            -> OtherBackend t
    return (b, s)

data GiveRefine = Give | Refine | Intro
  deriving (Eq, Show)

-- | A "give"-like action (give, refine, etc).
--
--   @give_gen ii rng s give_ref mk_newtxt@
--   acts on interaction point @ii@
--   occupying range @rng@,
--   placing the new content given by string @s@,
--   and replacing @ii@ by the newly created interaction points
--   in the state.
give_gen
  :: InteractionId
  -> Range
  -> String
  -> GiveRefine
  -> CommandM ()
give_gen ii rng s0 giveRefine = do
  let s = trim s0
  lift $ reportSLn "interaction.give" 20 $ "give_gen  " ++ s
  -- Andreas, 2015-02-26 if string is empty do nothing rather
  -- than giving a parse error.
  unless (null s) $ do
    let give_ref =
          case giveRefine of
            Give   -> B.give
            Refine -> B.refine
            Intro  -> B.refine
    -- save scope of the interaction point (for printing the given expr. later)
    scope     <- lift $ getInteractionScope ii
    -- parse string and "give", obtaining an abstract expression
    -- and newly created interaction points
    (time, (ae, ae0, iis)) <- maybeTimed $ lift $ do
        mis  <- getInteractionPoints
        reportSLn "interaction.give" 30 $ "interaction points before = " ++ show mis
        given <- B.parseExprIn ii rng s
        ae    <- give_ref ii Nothing given
        mis' <- getInteractionPoints
        reportSLn "interaction.give" 30 $ "interaction points after = " ++ show mis'
        return (ae, given, mis' List.\\ mis)
    -- favonia: backup the old scope for highlighting
    insertOldInteractionScope ii scope
    -- sort the new interaction points and put them into the state
    -- in replacement of the old interaction point
    iis       <- lift $ sortInteractionPoints iis
    modifyTheInteractionPoints $ replace ii iis
    -- print abstract expr
    ce        <- lift $ abstractToConcreteEnv (makeEnv scope) ae
    lift $ reportSLn "interaction.give" 30 $ unlines
      [ "ce = " ++ show ce
      , "scopePrecedence = " ++ show (scopePrecedence scope)
      ]
    -- if the command was @Give@, use the literal user input;
    -- Andreas, 2014-01-15, see issue 1020:
    -- Refine could solve a goal by introducing the sole constructor
    -- without arguments.  Then there are no interaction metas, but
    -- we still cannot just `give' the user string (which may be empty).
    -- WRONG: also, if no interaction metas were created by @Refine@
    -- WRONG: let literally = (giveRefine == Give || null iis) && rng /= noRange
    -- Ulf, 2015-03-30, if we're doing intro we can't do literal give since
    -- there is nothing in the hole (issue 1892).
    let literally = giveRefine /= Intro && ae == ae0 && rng /= noRange
    -- Ulf, 2014-01-24: This works for give since we're highlighting the string
    -- that's already in the buffer. Doing it before the give action means that
    -- the highlighting is moved together with the text when the hole goes away.
    -- To make it work for refine we'd have to adjust the ranges.
    when literally $ lift $ do
      printHighlightingInfo =<< generateTokenInfoFromString rng s
      highlightExpr ae
    putResponse $ Resp_GiveAction ii $ mkNewTxt literally ce
    lift $ reportSLn "interaction.give" 30 $ "putResponse GiveAction passed"
    -- display new goal set (if not measuring time)
    maybe (interpret Cmd_metas) (display_info . Info_Time) time
    lift $ reportSLn "interaction.give" 30 $ "interpret Cmd_metas passed"
  where
    -- Substitutes xs for x in ys.
    replace x xs ys = concatMap (\ y -> if y == x then xs else [y]) ys
    -- For @Give@ we can replace the ii by the user given input.
    mkNewTxt True  C.Paren{} = Give_Paren
    mkNewTxt True  _         = Give_NoParen
    -- Otherwise, we replace it by the reified value Agda computed.
    mkNewTxt False ce        = Give_String $ show ce

highlightExpr :: A.Expr -> TCM ()
highlightExpr e =
  local (\e -> e { envModuleNestingLevel = 0
                 , envHighlightingLevel  = NonInteractive
                 , envHighlightingMethod = Direct }) $
    generateAndPrintSyntaxInfo decl Full True
  where
    dummy = mkName_ (NameId 0 0) "dummy"
    info  = mkDefInfo (nameConcrete dummy) noFixity' PublicAccess ConcreteDef (getRange e)
    decl  = A.Axiom NoFunSig info defaultArgInfo Nothing (qnameFromList [dummy]) e

-- | Sorts interaction points based on their ranges.

sortInteractionPoints :: [InteractionId] -> TCM [InteractionId]
sortInteractionPoints is =
  map fst . List.sortBy (compare `on` snd) <$> do
    forM is $ \ i -> do
      (i,) <$> getInteractionRange i

-- | Pretty-prints the type of the meta-variable.

prettyTypeOfMeta :: B.Rewrite -> InteractionId -> TCM Doc
prettyTypeOfMeta norm ii = do
  form <- B.typeOfMeta norm ii
  case form of
    B.OfType _ e -> prettyATop e
    _            -> text <$> showATop form

-- | Pretty-prints the context of the given meta-variable.

prettyContext
  :: B.Rewrite      -- ^ Normalise?
  -> Bool           -- ^ Print the elements in reverse order?
  -> InteractionId
  -> TCM Doc
prettyContext norm rev ii = B.withInteractionId ii $ do
  ctx <- B.contextOfMeta ii norm
  es  <- mapM (prettyATop . B.ofExpr) ctx
  ns  <- mapM (showATop   . B.ofName) ctx
  return $ align 10 $ applyWhen rev reverse $
    filter (not . null . fst) $ zip ns $ map (text ":" <+>) es

-- | Create type of application of new helper function that would solve the goal.

cmd_helper_function :: B.Rewrite -> InteractionId -> Range -> String -> TCM Doc
cmd_helper_function norm ii r s = B.withInteractionId ii $ inTopContext $
  prettyATop =<< B.metaHelperType norm ii r s

-- | Displays the current goal, the given document, and the current
--   context.
--
--   Should not modify the state.

cmd_goal_type_context_and :: Doc -> B.Rewrite -> InteractionId -> Range ->
                             String -> StateT CommandState (TCMT IO) ()
cmd_goal_type_context_and doc norm ii _ _ = display_info . Info_GoalType =<< do
  lift $ do
    goal <- B.withInteractionId ii $ prettyTypeOfMeta norm ii
    ctx  <- prettyContext norm True ii
    return $ vcat
      [ text "Goal:" <+> goal
      , doc
      , text (replicate 60 '\x2014')
      , ctx
      ]

-- | Shows all the top-level names in the given module, along with
-- their types.

showModuleContents :: B.Rewrite -> Range -> String -> CommandM ()
showModuleContents norm rng s = display_info . Info_ModuleContents =<< do
  liftLocalState $ do
    (modules, types) <- B.moduleContents norm rng s
    types' <- forM types $ \ (x, t) -> do
      t <- TCP.prettyTCM t
      return (prettyShow x, text ":" <+> t)
    return $ vcat
      [ text "Modules"
      , nest 2 $ vcat $ map (text . show) modules
      , text "Names"
      , nest 2 $ align 10 types'
      ]

-- | Shows all the top-level names in scope which mention all the given
-- identifiers in their type.

searchAbout :: B.Rewrite -> Range -> String -> CommandM ()
searchAbout norm rg nm = do
  let tnm = trim nm
  unless (null tnm) $ do
    fancy <- lift $ B.atTopLevel $ do
       hits <- findMentions norm rg tnm
       forM hits $ \ (x, t) -> do
         t <- TCP.prettyTCM t
         return (prettyShow x, text ":" <+> t)
    display_info $ Info_SearchAbout $
      text "Definitions about" <+> text (List.intercalate ", " $ words nm) $$
      nest 2 (align 10 fancy)

-- | Explain why something is in scope.

whyInScope :: String -> CommandM ()
whyInScope s = display_info . Info_WhyInScope =<< do
  Just (file, _) <- gets theCurrentFile
  let cwd = takeDirectory $ filePath file
  liftLocalState $ do
    (v, xs, ms) <- B.whyInScope s
    explanation cwd v xs ms
  where
    explanation _ Nothing [] [] = TCP.text (s ++ " is not in scope.")
    explanation cwd v xs ms = TCP.vcat
      [ TCP.text (s ++ " is in scope as")
      , TCP.nest 2 $ TCP.vcat [variable v xs, modules ms]
      ]
      where
        prettyRange :: Range -> TCM Doc
        prettyRange r = text . show . (fmap . fmap) mkRel <$> do
          return r
        mkRel = Str . makeRelative cwd . filePath

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
              TCP.text "* a variable bound at" TCP.<+> TCP.prettyTCM (nameBindingSite $ localVar x)
            shadowing :: LocalVar -> TCM Doc
            shadowing (LocalVar _ _ [])    = TCP.text "shadowing"
            shadowing _ = TCP.text "in conflict with"
        names   xs = TCP.vcat $ map pName xs
        modules ms = TCP.vcat $ map pMod ms

        pKind DefName        = TCP.text "defined name"
        pKind ConName        = TCP.text "constructor"
        pKind FldName        = TCP.text "record field"
        pKind PatternSynName = TCP.text "pattern synonym"
        pKind MacroName      = TCP.text "macro name"
        pKind QuotableName   = TCP.text "quotable name"

        pName :: AbstractName -> TCM Doc
        pName a = TCP.sep
          [ TCP.text "* a"
            TCP.<+> pKind (anameKind a)
            TCP.<+> TCP.text (prettyShow $ anameName a)
          , TCP.nest 2 $ TCP.text "brought into scope by"
          ] TCP.$$
          TCP.nest 2 (pWhy (nameBindingSite $ qnameName $ anameName a) (anameLineage a))
        pMod :: AbstractModule -> TCM Doc
        pMod  a = TCP.sep
          [ TCP.text "* a module" TCP.<+> TCP.text (prettyShow $ amodName a)
          , TCP.nest 2 $ TCP.text "brought into scope by"
          ] TCP.$$
          TCP.nest 2 (pWhy (nameBindingSite $ qnameName $ mnameToQName $ amodName a) (amodLineage a))

        pWhy :: Range -> WhyInScope -> TCM Doc
        pWhy r Defined = TCP.text "- its definition at" TCP.<+> TCP.prettyTCM r
        pWhy r (Opened (C.QName x) w) | isNoName x = pWhy r w
        pWhy r (Opened m w) =
          TCP.text "- the opening of"
          TCP.<+> TCP.text (show m)
          TCP.<+> TCP.text "at"
          TCP.<+> TCP.prettyTCM (getRange m)
          TCP.$$
          pWhy r w
        pWhy r (Applied m w) =
          TCP.text "- the application of"
          TCP.<+> TCP.text (show m)
          TCP.<+> TCP.text "at"
          TCP.<+> TCP.prettyTCM (getRange m)
          TCP.$$
          pWhy r w

-- | Sets the command line options and updates the status information.

setCommandLineOpts :: CommandLineOptions -> CommandM ()
setCommandLineOpts opts = do
    lift $ TM.setCommandLineOptions opts
    displayStatus


-- | Computes some status information.
--
--   Does not change the state.

status :: CommandM Status
status = do
  cf <- gets theCurrentFile
  showImpl <- lift showImplicitArguments

  -- Check if the file was successfully type checked, and has not
  -- changed since. Note: This code does not check if any dependencies
  -- have changed, and uses a time stamp to check for changes.
  checked  <- lift $ case cf of
    Nothing     -> return False
    Just (f, t) -> do
      t' <- liftIO $ getModificationTime $ filePath f
      case t == t' of
        False -> return False
        True  -> do
          mm <- lookupModuleFromSource f
          case mm of
            Nothing -> return False -- work-around for Issue1007
            Just m  -> maybe False (not . miWarnings) <$> getVisitedModule m

  return $ Status { sShowImplicitArguments = showImpl
                  , sChecked               = checked
                  }

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

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

nameModifiers :: [String]
nameModifiers = "" : "'" : "''" : [show i | i <-[3..]]


-- | Parses and scope checks an expression (using the \"inside scope\"
-- as the scope), performs the given command with the expression as
-- input, and displays the result.

parseAndDoAtToplevel'
  :: (A.Expr -> TCM Doc)
     -- ^ The command to perform.
  -> (Doc -> DisplayInfo)
     -- ^ The name to use for the buffer displaying the output.
  -> String
     -- ^ The expression to parse.
  -> CommandM ()
parseAndDoAtToplevel' cmd title s = do
  (time, res) <- localStateCommandM $ do
    e <- lift $ runPM $ parse exprParser s
    maybeTimed (lift $ B.atTopLevel $
                cmd =<< concreteToAbstract_ e)
  display_info (title $ fromMaybe empty time $$ res)

parseAndDoAtToplevel :: (A.Expr -> TCM A.Expr) -> (Doc -> DisplayInfo) -> String -> CommandM ()
parseAndDoAtToplevel cmd = parseAndDoAtToplevel' (prettyA <=< cmd)

maybeTimed :: CommandM a -> CommandM (Maybe Doc, a)
maybeTimed work = do
  doTime <- lift $ hasVerbosity "profile.interactive" 10
  if not doTime then (Nothing,) <$> work else do
    (r, time) <- measureTime work
    return (Just $ text "Time:" <+> pretty time, r)

-- | Tell to highlight the code using the given highlighting
-- info (unless it is @Nothing@).

tellToUpdateHighlighting
  :: Maybe (HighlightingInfo, HighlightingMethod, ModuleToSource) -> IO [Response]
tellToUpdateHighlighting Nothing                = return []
tellToUpdateHighlighting (Just (info, method, modFile)) =
  return [Resp_HighlightingInfo info method modFile]

-- | Tells the Emacs mode to go to the first error position (if any).

tellEmacsToJumpToError :: Range -> [Response]
tellEmacsToJumpToError r =
  case rStart r of
    Nothing                                           -> []
    Just (Pn { srcFile = Strict.Nothing })            -> []
    Just (Pn { srcFile = Strict.Just f, posPos = p }) ->
       [ Resp_JumpToError (filePath f) p ]
