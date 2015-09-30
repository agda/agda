{-# OPTIONS -fno-cse #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Interaction.InteractionTop
  ( module Agda.Interaction.InteractionTop
  )
  where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import qualified Control.Exception as E
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Char as Char
import Data.Foldable (Foldable)
import Data.Function
import Data.List as List hiding (null)
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
import Agda.Interaction.Highlighting.Precise hiding (Postulate)
import qualified Agda.Interaction.Imports as Imp
import Agda.Interaction.Highlighting.Generate
import qualified Agda.Interaction.Highlighting.Range as H

import qualified Agda.Compiler.Epic.Compiler as Epic
import qualified Agda.Compiler.MAlonzo.Compiler as MAlonzo
import qualified Agda.Compiler.JS.Compiler as JS

import qualified Agda.Auto.Auto as Auto

import Agda.Utils.Except
  ( ExceptT
  , mkExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )

import Agda.Utils.FileName
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

------------------------------------------

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
  }

type OldInteractionScopes = Map InteractionId ScopeInfo

-- | Initial auxiliary interaction state

initCommandState :: CommandState
initCommandState = CommandState
  { theInteractionPoints = []
  , theCurrentFile       = Nothing
  , optionsOnReload      = defaultOptions
  , oldInteractionScopes = Map.empty
  }


-- | Monad for computing answers to interactive commands.
--
--   'CommandM' is 'TCM' extended with state 'CommandState'.

type CommandM = StateT CommandState TCM

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

-- | Run an 'IOTCM' value, catch the exceptions, emit output
--
--   If an error happens the state of 'CommandM' does not change,
--   but stPersistent may change (which contains successfully
--   loaded interfaces for example).

runInteraction :: IOTCM -> CommandM ()
runInteraction (IOTCM current highlighting highlightingMethod cmd)
    = handleNastyErrors
    $ inEmacs
    $ do
        current <- liftIO $ absolute current

        res <- (`catchErr` (return . Just)) $ do

            -- Raises an error if the given file is not the one currently
            -- loaded.
            cf <- gets theCurrentFile
            when (not (independent cmd) && Just current /= (fst <$> cf)) $
                lift $ typeError $ GenericError "Error: First load the file."

            withCurrentFile $ interpret cmd

            cf <- gets theCurrentFile
            when (Just current == (fst <$> cf)) $
                putResponse . Resp_InteractionPoints =<< gets theInteractionPoints
            return Nothing

        maybe (return ()) handleErr res

  where
    -- Preserves state so we can do unsolved meta highlighting
    catchErr :: CommandM a -> (TCErr -> CommandM a) -> CommandM a
    catchErr m h = do
      s       <- get
      -- If an independent command fails we should reset theCurrentFile (Issue853).
      let sErr | independent cmd = s { theCurrentFile = Nothing }
               | otherwise       = s
      (x, s') <- lift $ do disableDestructiveUpdate (runStateT m s)
         `catchError_` \ e ->
           runStateT (h e) sErr
      put s'
      return x

    inEmacs = liftCommandMT $ withEnv $ initEnv
            { envHighlightingLevel  = highlighting
            , envHighlightingMethod = highlightingMethod
            }

    -- | Handle nasty errors like stack space overflow (issue 637)
    -- We assume that the input action handles other kind of errors.
    handleNastyErrors :: CommandM () -> CommandM ()
    handleNastyErrors m = commandMToIO $ \ toIO ->
        toIO m `E.catch` \ (e :: E.SomeException) ->
          toIO $ handleErr $ Exception noRange $ text $ show e

    -- | Displays an error and instructs Emacs to jump to the site of the
    -- error. Because this function may switch the focus to another file
    -- the status information is also updated.
    handleErr e = do
        meta    <- lift $ computeUnsolvedMetaWarnings
        constr  <- lift $ computeUnsolvedConstraints
        err     <- lift $ errorHighlighting e
        modFile <- lift $ use stModuleToSource
        let info = compress $ mconcat
                     -- Errors take precedence over unsolved things.
                     [err, meta, constr]
        s <- lift $ prettyError e
        x <- lift $ optShowImplicit <$> use stPragmaOptions
        mapM_ putResponse $
            [ Resp_DisplayInfo $ Info_Error s ] ++
            tellEmacsToJumpToError (getRange e) ++
            [ Resp_HighlightingInfo info modFile ] ++
            [ Resp_Status $ Status { sChecked = False
                                   , sShowImplicitArguments = x
                                   } ]


----------------------------------------------------------------------------
-- | An interactive computation.

type Interaction = Interaction' Range

data Interaction' range
    -- | @cmd_load m includes@ loads the module in file @m@, using
    -- @includes@ as the include directories.
  = Cmd_load            FilePath [FilePath]

    -- | @cmd_compile b m includes@ compiles the module in file @m@ using
    -- the backend @b@, using @includes@ as the include directories.
  | Cmd_compile         Backend FilePath [FilePath]

  | Cmd_constraints

    -- | Show unsolved metas. If there are no unsolved metas but unsolved constraints
    -- show those instead.
  | Cmd_metas

    -- | Shows all the top-level names in the given module, along with
    -- their types. Uses the top-level scope.
  | Cmd_show_module_contents_toplevel
                        B.Rewrite
                        String

    -- | Shows all the top-level names in scope which mention all the given
    -- identifiers in their type.
  | Cmd_search_about_toplevel B.Rewrite String

  | Cmd_solveAll

    -- | Parse the given expression (as if it were defined at the
    -- top-level of the current module) and infer its type.
  | Cmd_infer_toplevel  B.Rewrite  -- Normalise the type?
                        String


    -- | Parse and type check the given expression (as if it were defined
    -- at the top-level of the current module) and normalise it.
  | Cmd_compute_toplevel Bool -- Ignore abstract?
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

  | Cmd_compute         Bool -- Ignore abstract?
                        InteractionId range String

  | Cmd_why_in_scope    InteractionId range String
  | Cmd_why_in_scope_toplevel String
    -- | Displays version of the running Agda
  | Cmd_show_version
        deriving (Read, Functor, Foldable, Traversable)


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
            deriving (Read, Functor, Foldable, Traversable)

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
exact s = readsToParse (show s) $ fmap (\x -> ((),x)) . stripPrefix s . dropWhile (==' ')

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

-- | Note that the grammar implemented by this instances matches an
-- old representation of ranges, not necessarily the current one.

instance Read a => Read (Range' a) where
    readsPrec = parseToReadsPrec $ do
                exact "Range"
                fmap intervalsToRange readParse
          `mplus` do
                exact "noRange"
                return noRange

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

interpret (Cmd_load m includes) =
  cmd_load' m includes True $ \_ -> interpret Cmd_metas

interpret (Cmd_compile b file includes) =
  cmd_load' file includes False $ \(i, mw) -> do
    case mw of
      Imp.NoWarnings -> do
        lift $ case b of
          MAlonzo -> MAlonzo.compilerMain True i
          MAlonzoNoMain -> MAlonzo.compilerMain False i
          Epic    -> Epic.compilerMain i
          JS      -> JS.compilerMain i
        display_info $ Info_CompilationOk
      Imp.SomeWarnings w ->
        display_info $ Info_Error $ unlines
          [ "You can only compile modules without unsolved metavariables"
          , "or termination checking problems."
          ]

interpret Cmd_constraints =
    display_info . Info_Constraints . unlines . map show =<< lift B.getConstraints

interpret Cmd_metas = do -- CL.showMetas []
  ms <- lift $ showOpenMetas
  -- If we do not have open metas, but open constaints, display those.
  ifM (return (null ms) `and2M` do not . null <$> lift B.getConstraints)
    {-then-} (interpret Cmd_constraints)
    {-else-} (display_info $ Info_AllGoals $ unlines ms)

interpret (Cmd_show_module_contents_toplevel norm s) =
  liftCommandMT B.atTopLevel $ showModuleContents norm noRange s

interpret (Cmd_search_about_toplevel norm s) =
  liftCommandMT B.atTopLevel $ searchAbout norm noRange s

interpret Cmd_solveAll = do
  out <- lift $ mapM lowr =<< B.getSolvedInteractionPoints False -- only solve metas which have a proper instantiation, i.e., not another meta
  putResponse $ Resp_SolveAll out
  where
      lowr (i, m, e) = do
        mi <- getMetaInfo <$> lookupMeta m
        e <- withMetaInfo mi $ lowerMeta <$> abstractToConcreteCtx TopCtx e
        return (i, e)

interpret (Cmd_infer_toplevel norm s) =
  parseAndDoAtToplevel (B.typeInCurrent norm) Info_InferredType s

interpret (Cmd_compute_toplevel ignore s) =
  parseAndDoAtToplevel (allowNonTerminatingReductions .
                        if ignore then ignoreAbstractMode . c
                                  else inConcreteMode . c)
                       Info_NormalForm
                       s
  where c = B.evalInCurrent

interpret (ShowImplicitArgs showImpl) = do
  opts <- lift commandLineOptions
  setCommandLineOptions' $
    opts { optPragmaOptions =
             (optPragmaOptions opts) { optShowImplicit = showImpl } }

interpret ToggleImplicitArgs = do
  opts <- lift commandLineOptions
  let ps = optPragmaOptions opts
  setCommandLineOptions' $
    opts { optPragmaOptions =
             ps { optShowImplicit = not $ optShowImplicit ps } }

interpret (Cmd_load_highlighting_info source) = do
    -- Make sure that the include directories have
    -- been set.
    setCommandLineOptions' =<< lift commandLineOptions

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
                return $ Just (iHighlighting $ miInterface mi, modFile)
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
    [s]   -> do
      interpret $ Cmd_refine ii rng s
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
  (res, msg) <- lift $ Auto.auto ii rng s
  case res of
   Left xs -> do
    lift $ reportSLn "auto" 10 $ "Auto produced the following solutions " ++ show xs
    forM_ xs $ \(ii, s) -> do
      -- Andreas, 2014-07-05 Issue 1226:
      -- For highlighting, Resp_GiveAction needs to access
      -- the @oldInteractionScope@s of the interaction points solved by Auto.
      -- We dig them out from the state before Auto was invoked.
      insertOldInteractionScope ii =<< lift (localState (put st >> getInteractionScope ii))
      -- Andreas, 2014-07-07: NOT TRUE:
      -- -- Andreas, 2014-07-05: The following should be obsolete,
      -- -- as Auto has removed the interaction points already:
      -- modifyTheInteractionPoints $ filter (/= ii)
      putResponse $ Resp_GiveAction ii $ Give_String s
    -- Andreas, 2014-07-07: Remove the interaction points in one go.
    modifyTheInteractionPoints (\\ (map fst xs))
    case msg of
     Nothing -> interpret Cmd_metas
     Just msg -> display_info $ Info_Auto msg
   Right (Left cs) -> do
    case msg of
     Nothing -> return ()
     Just msg -> display_info $ Info_Auto msg
    putResponse $ Resp_MakeCase R.Function cs
   Right (Right s) -> give_gen ii rng s Refine

interpret (Cmd_context norm ii _ _) =
  display_info . Info_Context =<< lift (prettyContext norm False ii)

interpret (Cmd_helper_function norm ii rng s) =
  display_info . Info_HelperFunction =<< lift (cmd_helper_function norm ii rng s)

interpret (Cmd_infer norm ii rng s) =
  display_info . Info_InferredType
    =<< lift (B.withInteractionId ii
          (prettyATop =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s))

interpret (Cmd_goal_type norm ii _ _) =
  display_info . Info_CurrentGoal
    =<< lift (B.withInteractionId ii $ prettyTypeOfMeta norm ii)

interpret (Cmd_goal_type_context norm ii rng s) =
  cmd_goal_type_context_and empty norm ii rng s

interpret (Cmd_goal_type_context_infer norm ii rng s) = do
  -- In case of the empty expression to type, don't fail with
  -- a stupid parse error, but just fall back to
  -- Cmd_goal_type_context.
  have <- if all Char.isSpace s then return empty else do
    typ <- lift $ B.withInteractionId ii $
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
  (casectxt , cs) <- lift $ makeCase ii rng s
  liftCommandMT (B.withInteractionId ii) $ do
    hidden <- lift $ showImplicitArguments
    pcs <- lift $ mapM prettyA $ List.map (extlam_dropLLifted casectxt hidden) cs
    putResponse $ Resp_MakeCase (makeCaseVariant casectxt) (List.map (extlam_dropName casectxt . render) pcs)
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
    extlam_dropLLifted (Just (ExtLamInfo h nh)) hidden (A.Clause (A.LHS info A.LHSProj{} ps) rhs decl catchall) = __IMPOSSIBLE__
    extlam_dropLLifted (Just (ExtLamInfo h nh)) hidden (A.Clause (A.LHS info (A.LHSHead name nps) ps) rhs decl catchall)
      = let n = if hidden then h + nh else nh
        in
         (A.Clause (A.LHS info (A.LHSHead name (drop n nps)) ps) rhs decl catchall)

interpret (Cmd_compute ignore ii rng s) = do
  e <- lift $ B.parseExprIn ii rng s
  d <- lift $ B.withInteractionId ii $ do
         let c = B.evalInCurrent e
         v <- if ignore then ignoreAbstractMode c else c
         prettyATop v
  display_info $ Info_NormalForm d

interpret Cmd_show_version = display_info Info_Version

-- | Print open metas nicely.
showOpenMetas :: TCM [String]
showOpenMetas = do
  ims <- B.typesOfVisibleMetas B.AsIs
  di <- forM ims $ \ i ->
    B.withInteractionId (B.outputFormId $ B.OutputForm noRange 0 i) $
      showATop i
  -- Show unsolved implicit arguments simplified.
  dh <- mapM showA' =<< B.typesOfHiddenMetas B.Simplified
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


-- | @cmd_load' file includes unsolvedOk cmd@
--   loads the module in file @file@,
--   using @includes@ as the include directories.
--
-- If type checking completes without any exceptions having been
-- encountered then the command @cmd r@ is executed, where @r@ is the
-- result of 'Imp.typeCheckMain'.

cmd_load' :: FilePath -> [FilePath]
          -> Bool -- ^ Allow unsolved meta-variables?
          -> ((Interface, Imp.MaybeWarnings) -> CommandM ())
          -> CommandM ()
cmd_load' file includes unsolvedOK cmd = do
    f <- liftIO $ absolute file
    ex <- liftIO $ doesFileExist $ filePath f
    lift $ TM.setIncludeDirs includes $
      if ex then ProjectRoot f else CurrentDir

    -- Forget the previous "current file" and interaction points.
    modify $ \st -> st { theInteractionPoints = []
                       , theCurrentFile       = Nothing
                       }

    t <- liftIO $ getModificationTime file

    -- All options are reset when a file is reloaded, including the
    -- choice of whether or not to display implicit arguments. (At
    -- this point the include directories have already been set, so
    -- they are preserved.)
    opts <- lift $ commandLineOptions
    defaultOptions <- gets optionsOnReload
    setCommandLineOptions' $
      Lenses.setIncludeDirs (optIncludeDirs opts) $
      mapPragmaOptions (\ o -> o { optAllowUnsolved = unsolvedOK }) $
      defaultOptions

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

    ok <- lift $ Imp.typeCheckMain f

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

data Backend = MAlonzo
             | MAlonzoNoMain
             | Epic | JS
    deriving (Show, Read)

data GiveRefine = Give | Refine
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
    -- save scope of the interaction point (for printing the given expr. later)
    scope     <- lift $ getInteractionScope ii
    -- parse string and "give", obtaining an abstract expression
    -- and newly created interaction points
    (time, (ae, iis)) <- maybeTimed (lift $ do
        mis  <- getInteractionPoints
        reportSLn "interaction.give" 30 $ "interaction points before = " ++ show mis
        ae   <- give_ref ii Nothing =<< B.parseExprIn ii rng s
        mis' <- getInteractionPoints
        reportSLn "interaction.give" 30 $ "interaction points after = " ++ show mis'
        return (ae, mis' \\ mis))
    -- favonia: backup the old scope for highlighting
    insertOldInteractionScope ii scope
    -- sort the new interaction points and put them into the state
    -- in replacement of the old interaction point
    iis       <- lift $ sortInteractionPoints iis
    modifyTheInteractionPoints $ replace ii iis
    -- print abstract expr
    ce        <- lift $ abstractToConcreteEnv (makeEnv scope) ae
    lift $ reportSLn "interaction.give" 30 $ "ce = " ++ show ce
    -- if the command was @Give@, use the literal user input;
    -- Andreas, 2014-01-15, see issue 1020:
    -- Refine could solve a goal by introducing the sole constructor
    -- without arguments.  Then there are no interaction metas, but
    -- we still cannot just `give' the user string (which may be empty).
    -- WRONG: also, if no interaction metas were created by @Refine@
    -- WRONG: let literally = (giveRefine == Give || null iis) && rng /= noRange
    let literally = giveRefine == Give && rng /= noRange
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
    generateAndPrintSyntaxInfo decl Full
  where
    dummy = mkName_ (NameId 0 0) "dummy"
    info  = mkDefInfo (nameConcrete dummy) noFixity' PublicAccess ConcreteDef (getRange e)
    decl  = A.Axiom NoFunSig info defaultArgInfo (qnameFromList [dummy]) e

-- | Sorts interaction points based on their ranges.

sortInteractionPoints :: [InteractionId] -> TCM [InteractionId]
sortInteractionPoints is =
  map fst . sortBy (compare `on` snd) <$> do
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
  let shuffle = if rev then reverse else id
  return $ align 10 $ filter (not . null. fst) $ shuffle $ zip ns (map (text ":" <+>) es)

-- | Create type of application of new helper function that would solve the goal.

cmd_helper_function :: B.Rewrite -> InteractionId -> Range -> String -> TCM Doc
cmd_helper_function norm ii r s = B.withInteractionId ii $ inTopContext $
  prettyATop =<< B.metaHelperType norm ii r s

-- | Displays the current goal, the given document, and the current
-- context.

cmd_goal_type_context_and :: Doc -> B.Rewrite -> InteractionId -> Range ->
                             String -> StateT CommandState (TCMT IO) ()
cmd_goal_type_context_and doc norm ii _ _ = do
  goal <- lift $ B.withInteractionId ii $ prettyTypeOfMeta norm ii
  ctx  <- lift $ prettyContext norm True ii
  display_info $ Info_GoalType
                (text "Goal:" <+> goal $+$
                 doc $+$
                 text (replicate 60 '\x2014') $+$
                 ctx)

-- | Shows all the top-level names in the given module, along with
-- their types.

showModuleContents :: B.Rewrite -> Range -> String -> CommandM ()
showModuleContents norm rng s = do
  (modules, types) <- lift $ B.moduleContents norm rng s
  types' <- lift $ forM types $ \ (x, t) -> do
     t <- TCP.prettyTCM t
     return (show x, text ":" <+> t)
  display_info $ Info_ModuleContents $
    text "Modules" $$
    nest 2 (vcat $ map (text . show) modules) $$
    text "Names" $$
    nest 2 (align 10 types')

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
         return (show x, text ":" <+> t)
    display_info $ Info_SearchAbout $
      text "Definitions about" <+> text (intercalate ", " $ words nm) $$
      nest 2 (align 10 fancy)

-- | Explain why something is in scope.

whyInScope :: String -> CommandM ()
whyInScope s = do
  (v, xs, ms) <- lift $ B.whyInScope s
  cwd <- do
    Just (file, _) <- gets $ theCurrentFile
    return $ takeDirectory $ filePath file
  display_info . Info_WhyInScope =<< do lift $ explanation cwd v xs ms
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
            shadowing LocalVar{}    = TCP.text "shadowing"
            shadowing ShadowedVar{} = TCP.text "in conflict with"
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

setCommandLineOptions' :: CommandLineOptions -> CommandM ()
setCommandLineOptions' opts = do
    lift $ TM.setCommandLineOptions opts
    displayStatus


-- | Computes some status information.

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
          mm <- Map.lookup f <$> sourceToModule
          case mm of
            Nothing -> return False -- work-around for Issue1007
            Just m  -> not . miWarnings . fromMaybe __IMPOSSIBLE__ <$> getVisitedModule m

  return $ Status { sShowImplicitArguments = showImpl
                  , sChecked               = checked
                  }

-- | Displays\/updates status information.

displayStatus :: CommandM ()
displayStatus =
  putResponse . Resp_Status  =<< status

-- | @display_info@ does what @'display_info'' False@ does, but
-- additionally displays some status information (see 'status' and
-- 'displayStatus').

display_info :: DisplayInfo -> CommandM ()
display_info info = do
  displayStatus
  putResponse $ Resp_DisplayInfo info

-- UNUSED
-- takenNameStr :: TCM [String]
-- takenNameStr = do
--   xss <- sequence [ List.map (fst . unDom) <$> getContext
--                   , Map.keys <$> asks envLetBindings
--                   , List.map qnameName . HMap.keys . sigDefinitions <$> getSignature
--                ]
--   return $ concat [ parts $ nameConcrete x | x <- concat xss]
--   where
--     parts x = [ s | Id s <- nameParts x ]

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

nameModifiers :: [String]
nameModifiers = "" : "'" : "''" : [show i | i <-[3..]]


-- | Kill meta numbers and ranges from all metas (@?@ and @_@).
lowerMeta :: (C.ExprLike a) => a -> a
lowerMeta = C.mapExpr kill where
  kill e =
    case e of
      C.QuestionMark{} -> preMeta
      C.Underscore{}   -> preUscore
      C.App{}          -> case appView e of
        C.AppView (C.QuestionMark _ _) _ -> preMeta
        C.AppView (C.Underscore   _ _) _ -> preUscore
        _ -> e
      C.Paren r q@(C.QuestionMark _ Nothing) -> q
      _ -> e

  preMeta   = C.QuestionMark noRange Nothing
  preUscore = C.Underscore   noRange Nothing


-- | Parses and scope checks an expression (using the \"inside scope\"
-- as the scope), performs the given command with the expression as
-- input, and displays the result.

parseAndDoAtToplevel
  :: (A.Expr -> TCM A.Expr)
     -- ^ The command to perform.
  -> (Doc -> DisplayInfo)
     -- ^ The name to use for the buffer displaying the output.
  -> String
     -- ^ The expression to parse.
  -> CommandM ()
parseAndDoAtToplevel cmd title s = do
  e   <- liftIO $ parse exprParser s
  (time, res) <-
    maybeTimed (lift $ B.atTopLevel $
                prettyA =<< cmd =<< concreteToAbstract_ e)
  display_info (title $ fromMaybe empty time $$ res)

maybeTimed :: CommandM a -> CommandM (Maybe Doc, a)
maybeTimed work = do
  doTime <- lift $ hasVerbosity "profile.interactive" 10
  if not doTime then (Nothing,) <$> work else do
    (r, time) <- measureTime work
    return (Just $ text "Time:" <+> pretty time, r)

-- | Tell to highlight the code using the given highlighting
-- info (unless it is @Nothing@).

tellToUpdateHighlighting
  :: Maybe (HighlightingInfo, ModuleToSource) -> IO [Response]
tellToUpdateHighlighting Nothing                = return []
tellToUpdateHighlighting (Just (info, modFile)) =
  return [Resp_HighlightingInfo info modFile]

-- | Tells the Emacs mode to go to the first error position (if any).

tellEmacsToJumpToError :: Range -> [Response]
tellEmacsToJumpToError r =
  case rStart r of
    Nothing                                           -> []
    Just (Pn { srcFile = Strict.Nothing })            -> []
    Just (Pn { srcFile = Strict.Just f, posPos = p }) ->
       [ Resp_JumpToError (filePath f) p ]
