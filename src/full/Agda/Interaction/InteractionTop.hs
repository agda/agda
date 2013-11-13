{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, TupleSections,
             MultiParamTypeClasses, Rank2Types,
             GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# OPTIONS -fno-cse #-}

module Agda.Interaction.InteractionTop
  ( module Agda.Interaction.InteractionTop
  )
  where

import Control.Applicative hiding (empty)
import qualified Control.Exception as E
import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import Data.Function
import Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import Data.Monoid

import System.Directory

import Agda.TypeChecking.Monad as TM
  hiding (initState, setCommandLineOptions)
import qualified Agda.TypeChecking.Monad as TM
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
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete hiding (withScope)

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.MakeCase
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

import Agda.Utils.FileName
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Pretty
import Agda.Utils.Time

#include "../undefined.h"
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
  }

-- | Initial auxiliary interaction state

initCommandState :: CommandState
initCommandState = CommandState
  { theInteractionPoints = []
  , theCurrentFile       = Nothing
  , optionsOnReload      = defaultOptions
  }


-- | Monad for computing answers to interactive commands.
--
--   'CommandM' is 'TCM' extended with state 'CommandState'.

type CommandM a = StateT CommandState TCM a

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

-- | 'runSafeTCM' runs a safe 'TMC' action (a 'TCM' action which cannot fail)

runSafeTCM :: TCM a -> TCState -> IO (a, TCState)
runSafeTCM m st = do
    x <- runTCM $ do
        put st
        a <- m
        st <- get
        return (a, st)
    case x of
        Right x -> return x
        Left _  -> __IMPOSSIBLE__   -- cannot happen if 'm' is safe

-- | Lift a TCM action transformer to a CommandM action transformer.

liftCommandMT :: (forall a . TCM a -> TCM a) -> CommandM a -> CommandM a
liftCommandMT f m = revLift runStateT lift $ f . ($ m)

-- | Put a response by the callback function given by 'stInteractionOutputCallback'.

putResponse :: Response -> CommandM ()
putResponse = lift . appInteractionOutputCallback


-- | A Lens for 'theInteractionPoints'.

modifyInteractionPoints :: ([InteractionId] -> [InteractionId]) -> CommandM ()
modifyInteractionPoints f = modify $ \ s ->
  s { theInteractionPoints = f (theInteractionPoints s) }


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

            interpret cmd

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
      (x, s') <- lift (runStateT m s `catchError_` \e -> runStateT (h e) s)
      put s'
      return x

    inEmacs = liftCommandMT $ withEnv $ initEnv
            { envEmacs              = True
            , envHighlightingLevel  = highlighting
            , envHighlightingMethod = highlightingMethod
            }

    -- | Handle nasty errors like stack space overflow (issue 637)
    -- We assume that the input action handles other kind of errors.
    handleNastyErrors :: CommandM () -> CommandM ()
    handleNastyErrors m = commandMToIO $ \toIO ->
        toIO m `E.catch` (toIO . handleErr . Exception noRange . (show :: E.SomeException -> String))

    -- | Displays an error and instructs Emacs to jump to the site of the
    -- error. Because this function may switch the focus to another file
    -- the status information is also updated.
    handleErr e = do
        meta    <- lift $ computeUnsolvedMetaWarnings
        constr  <- lift $ computeUnsolvedConstraints
        modFile <- lift $ gets stModuleToSource
        let info = compress $ meta `mappend` constr
        s <- lift $ prettyError e
        x <- lift . gets $ optShowImplicit . stPragmaOptions
        let r = getRange e
        mapM_ putResponse $
            [ Resp_DisplayInfo $ Info_Error s ] ++
            tellEmacsToJumpToError (getRange e) ++
            [ Resp_HighlightingInfo (noHighlightingInRange (H.rToR r) info) modFile ] ++
            [ Resp_Status $ Status { sChecked = False
                                   , sShowImplicitArguments = x
                                   } ]


----------------------------------------------------------------------------
-- | An interactive computation.

data Interaction
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
                        String

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

  | Cmd_give            InteractionId Range String

  | Cmd_refine          InteractionId Range String

  | Cmd_intro           Bool InteractionId Range String

  | Cmd_refine_or_intro Bool InteractionId Range String

  | Cmd_auto            InteractionId Range String

  | Cmd_context         B.Rewrite InteractionId Range String

  | Cmd_helper_function B.Rewrite InteractionId Range String

  | Cmd_infer           B.Rewrite InteractionId Range String

  | Cmd_goal_type       B.Rewrite InteractionId Range String

    -- | Displays the current goal and context.
  | Cmd_goal_type_context B.Rewrite InteractionId Range String

    -- | Displays the current goal and context /and/ infers the type of an
    -- expression.
  | Cmd_goal_type_context_infer
                        B.Rewrite InteractionId Range String

    -- | Shows all the top-level names in the given module, along with
    -- their types. Uses the scope of the given goal.
  | Cmd_show_module_contents
                        InteractionId Range String

  | Cmd_make_case       InteractionId Range String

  | Cmd_compute         Bool -- Ignore abstract?
                        InteractionId Range String
        deriving Read

data IOTCM
    = IOTCM
        FilePath
         -- -^ The current file. If this file does not match
         -- 'theCurrentFile, and the 'Interaction' is not
         -- \"independent\", then an error is raised.
        HighlightingLevel
        HighlightingMethod
        Interaction
         -- -^ What to do
            deriving Read

---------------------------------------------------------
-- Read instances


-- | The 'Parse' monad.
--   'StateT' state holds the remaining input.

type Parse a = ErrorT String (StateT String Identity) a

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
parseToReadsPrec p i s = case runIdentity . flip runStateT s . runErrorT $ parens' p of
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

instance Read Range where
    readsPrec = parseToReadsPrec $ do
                exact "Range"
                fmap Range readParse
          `mplus` do
                exact "noRange"
                return noRange

instance Read Interval where
    readsPrec = parseToReadsPrec $ do
        exact "Interval"
        liftM2 Interval readParse readParse

instance Read AbsolutePath where
    readsPrec = parseToReadsPrec $ do
        exact "mkAbsolute"
        fmap mkAbsolute readParse

instance Read Position where
    readsPrec = parseToReadsPrec $ do
        exact "Pn"
        liftM4 Pn readParse readParse readParse readParse

---------------------------------------------------------

-- | Can the command run even if the relevant file has not been loaded
--   into the state?

independent :: Interaction -> Bool
independent (Cmd_load {})    = True
independent (Cmd_compile {}) = True
independent (Cmd_load_highlighting_info {}) = True
independent _                = False

-- | Interpret an interaction

interpret :: Interaction -> CommandM ()

interpret (Cmd_load m includes) =
  cmd_load' m includes True $ \_ -> interpret Cmd_metas

interpret (Cmd_compile b file includes) =
  cmd_load' file includes False $ \(i, mw) -> do
    case mw of
      Nothing -> do
        lift $ case b of
          MAlonzo -> MAlonzo.compilerMain i
          Epic    -> Epic.compilerMain i
          JS      -> JS.compilerMain i
        display_info $ Info_CompilationOk
      Just w ->
        display_info $ Info_Error $ unlines
          [ "You can only compile modules without unsolved metavariables"
          , "or termination checking problems."
          ]

interpret Cmd_constraints =
    display_info . Info_Constraints . unlines . map show =<< lift B.getConstraints

interpret Cmd_metas = do -- CL.showMetas []
  ims <- lift $ B.typesOfVisibleMetas B.AsIs
  -- Show unsolved implicit arguments normalised.
  hms <- lift $ B.typesOfHiddenMetas B.Normalised
  if not $ null ims && null hms
    then do
      di <- lift $ forM ims $ \i -> B.withInteractionId (B.outputFormId $ B.OutputForm noRange 0 i) (showATop i)
      dh <- lift $ mapM showA' hms
      display_info $ Info_AllGoals $ unlines $ di ++ dh
    else do
      cs <- lift B.getConstraints
      if null cs
        then display_info $ Info_AllGoals ""
        else interpret Cmd_constraints
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

interpret (Cmd_show_module_contents_toplevel s) =
  liftCommandMT B.atTopLevel $ showModuleContents noRange s

interpret Cmd_solveAll = do
  out <- lift $ mapM lowr =<< B.getSolvedInteractionPoints
  putResponse $ Resp_SolveAll out
  where
      lowr (i, m, e) = do
        mi <- getMetaInfo <$> lookupMeta m
        e <- withMetaInfo mi $ lowerMeta <$> abstractToConcreteCtx TopCtx e
        return (i, e)

interpret (Cmd_infer_toplevel norm s) =
  parseAndDoAtToplevel (B.typeInCurrent norm) Info_InferredType s

interpret (Cmd_compute_toplevel ignore s) =
  parseAndDoAtToplevel (if ignore then ignoreAbstractMode . c
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
      case ex of
        False -> return Nothing
        True  -> do
          mmi <- (getVisitedModule =<<
                    moduleName =<< liftIO (absolute source))
                   `catchError`
                 \_ -> return Nothing
          case mmi of
            Nothing -> return Nothing
            Just mi -> do
              sourceT <- liftIO $ getModificationTime source
              if sourceT <= miTimeStamp mi
               then do
                modFile <- gets stModuleToSource
                return $ Just (iHighlighting $ miInterface mi, modFile)
               else
                return Nothing
    mapM_ putResponse resp

interpret (Cmd_give ii rng s) = give_gen ii rng s B.give $ \rng s ce ->
  case ce of
    ce | rng == noRange -> Give_String $ show ce
    C.Paren _ _ -> Give_Paren
    _            -> Give_NoParen

interpret (Cmd_refine ii rng s) = give_gen ii rng s B.refine $ \_ s -> Give_String . show

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
  (if null s then Cmd_intro pmLambda else Cmd_refine) ii r s

interpret (Cmd_auto ii rng s) = do
  (res, msg) <- lift $ Auto.auto ii rng s
  case res of
   Left xs -> do
    forM_ xs $ \(ii, s) -> do
      modifyInteractionPoints $ filter (/= ii)
      putResponse $ Resp_GiveAction ii $ Give_String s
    case msg of
     Nothing -> interpret Cmd_metas
     Just msg -> display_info $ Info_Auto msg
   Right (Left cs) -> do
    case msg of
     Nothing -> return ()
     Just msg -> display_info $ Info_Auto msg
    putResponse $ Resp_MakeCase R.Function cs
   Right (Right s) -> give_gen ii rng s B.refine (\_ s -> Give_String . show)

interpret (Cmd_context norm ii _ _) =
  display_info . Info_Context =<< lift (prettyContext norm False ii)

interpret (Cmd_helper_function norm ii rng s) =
  display_info . Info_HelperFunction =<< lift (doStuff norm ii rng s)

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
  typ <- lift $ B.withInteractionId ii $
           prettyATop =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s
  cmd_goal_type_context_and (text "Have:" <+> typ) norm ii rng s

interpret (Cmd_show_module_contents ii rng s) =
  liftCommandMT (B.withInteractionId ii) $ showModuleContents rng s

interpret (Cmd_make_case ii rng s) = do
  (casectxt , cs) <- lift $ makeCase ii rng s
  liftCommandMT (B.withInteractionId ii) $ do
    hidden <- lift $ showImplicitArguments
    pcs <- lift $ mapM prettyA $ List.map (extlam_dropLLifted casectxt hidden) cs
    putResponse $ Resp_MakeCase (makeCaseVariant casectxt) (List.map (extlam_dropName casectxt . render) pcs)
  where
    render = renderStyle (style { mode = OneLineMode })

    makeCaseVariant :: CaseContext -> MakeCaseVariant
    makeCaseVariant FunctionDef          = R.Function
    makeCaseVariant (ExtendedLambda _ _) = R.ExtendedLambda

    -- very dirty hack, string manipulation by dropping the function name
    -- and replacing the last " = " with " -> ". It's important not to replace
    -- the equal sign in named implicit with an arrow!
    extlam_dropName :: CaseContext -> String -> String
    extlam_dropName FunctionDef x = x
    extlam_dropName (ExtendedLambda _ _) x
        = unwords $ reverse $ replEquals $ reverse $ drop 1 $ words x
      where
        replEquals ("=" : ws) = "→" : ws
        replEquals (w   : ws) = w : replEquals ws
        replEquals []         = []

    -- Drops pattern added to extended lambda functions when lambda lifting them
    extlam_dropLLifted :: CaseContext -> Bool -> A.Clause -> A.Clause
    extlam_dropLLifted FunctionDef _ x = x
    extlam_dropLLifted (ExtendedLambda h nh) hidden (A.Clause (A.LHS info (A.LHSProj{}) ps) rhs decl) = __IMPOSSIBLE__
    extlam_dropLLifted (ExtendedLambda h nh) hidden (A.Clause (A.LHS info (A.LHSHead name nps) ps) rhs decl)
      = let n = if hidden then h + nh else nh
        in
         (A.Clause (A.LHS info (A.LHSHead name (drop n nps)) ps) rhs decl)

interpret (Cmd_compute ignore ii rng s) = do
  e <- lift $ B.parseExprIn ii rng s
  d <- lift $ B.withInteractionId ii $ do
         let c = B.evalInCurrent e
         v <- if ignore then ignoreAbstractMode c else c
         prettyATop v
  display_info $ Info_NormalForm d

type GoalCommand = InteractionId -> Range -> String -> Interaction

-- | @cmd_load' m includes cmd cmd2@ loads the module in file @m@,
-- using @includes@ as the include directories.
--
-- If type checking completes without any exceptions having been
-- encountered then the command @cmd r@ is executed, where @r@ is the
-- result of 'Imp.typeCheck'.

cmd_load' :: FilePath -> [FilePath]
          -> Bool -- ^ Allow unsolved meta-variables?
          -> ((Interface, Maybe Warnings) -> CommandM ())
          -> CommandM ()
cmd_load' file includes unsolvedOK cmd = do
    f <- liftIO $ absolute file
    ex <- liftIO $ doesFileExist $ filePath f
    lift $ setIncludeDirs includes $
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
      defaultOptions { optIncludeDirs   = optIncludeDirs opts
                     , optPragmaOptions =
                         (optPragmaOptions defaultOptions)
                           { optAllowUnsolved = unsolvedOK
                           }
                     }

    -- Reset the state, preserving options and decoded modules. Note
    -- that if the include directories have changed, then the decoded
    -- modules are reset when cmd_load' is run by ioTCM.
    lift resetState

    -- Clear the info buffer to make room for information about which
    -- module is currently being type-checked.
    putResponse Resp_ClearRunningInfo

    -- Remove any prior syntax highlighting.
    putResponse Resp_ClearHighlighting

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

-- | Available backends.

data Backend = MAlonzo | Epic | JS
    deriving (Show, Read)

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
  -> (InteractionId -> Maybe Range -> A.Expr -> TCM (A.Expr, [InteractionId]))
  -> (Range -> String -> C.Expr -> GiveResult)
  -> StateT CommandState TCM ()
give_gen ii rng s give_ref mk_newtxt = do
  -- save scope of the interaction point (for printing the given expr. later)
  scope     <- lift $ getInteractionScope ii
  -- parse string and "give", obtaining an abstract expression
  -- and newly created interaction points
  (ae, iis) <- lift $ give_ref ii Nothing =<< B.parseExprIn ii rng s
  -- sort the new interaction points and put them into the state
  -- in replacement of the old interaction point
  iis       <- lift $ sortInteractionPoints iis
  modifyInteractionPoints $ replace ii iis
  -- print abstract expr
  ce        <- lift $ abstractToConcreteEnv (makeEnv scope) ae
  putResponse $ Resp_GiveAction ii $ mk_newtxt rng s ce
  -- display new goal set
  interpret Cmd_metas
  where
    -- Substitutes xs for x in ys.
    replace x xs ys = concatMap (\y -> if y == x then xs else [y]) ys

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

-- | Do stuff.

doStuff :: B.Rewrite -> InteractionId -> Range -> String -> TCM Doc
doStuff norm ii r s = B.withInteractionId ii $ inTopContext $
  prettyATop =<< B.metaHelperType norm ii r s

-- | Displays the current goal, the given document, and the current
-- context.

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

showModuleContents :: Range -> String -> CommandM ()
showModuleContents rng s = do
  (modules, types) <- lift $ B.moduleContents rng s
  types' <- lift $ forM types $ \ (x, t) -> do
     t <- prettyTCM t
     return (show x, text ":" <+> t)
  display_info $ Info_ModuleContents $
    text "Modules" $$
    nest 2 (vcat $ map (text . show) modules) $$
    text "Names" $$
    nest 2 (align 10 types')

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
        True  ->
          not . miWarnings . fromMaybe __IMPOSSIBLE__ <$> do
            getVisitedModule =<< do
              Map.findWithDefault __IMPOSSIBLE__ f <$> sourceToModule

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

takenNameStr :: TCM [String]
takenNameStr = do
  xss <- sequence [ List.map (fst . unDom) <$> getContext
                  , Map.keys <$> asks envLetBindings
                  , List.map qnameName . HMap.keys . sigDefinitions <$> getSignature
		  ]
  return $ concat [ parts $ nameConcrete x | x <- concat xss]
  where
    parts x = [ s | Id s <- nameParts x ]

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

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


{- Andreas, 2013-11-04 replaced this boilerplate by generic boilerplate
   see Agda.Syntax.Concrete.Generic

class LowerMeta a where
  lowerMeta :: a -> a

instance LowerMeta C.Expr where
  lowerMeta = go where
    go e = case e of
      Ident _            -> e
      C.Lit _            -> e
      C.QuestionMark _ _ -> preMeta
      C.Underscore _ _   -> preUscore
      C.App r e1 ae2     -> case appView e of
        C.AppView (C.QuestionMark _ _) _ -> preMeta
        C.AppView (C.Underscore   _ _) _ -> preUscore
        _ -> C.App r (go e1) (lowerMeta ae2)
      C.WithApp r e es	 -> C.WithApp r (lowerMeta e) (lowerMeta es)
      C.Lam r bs e1      -> C.Lam r (lowerMeta bs) (go e1)
      C.AbsurdLam r h    -> C.AbsurdLam r h
      C.ExtendedLam r cs -> C.ExtendedLam r cs
      C.Fun r ae1 e2     -> C.Fun r (lowerMeta ae1) (go e2)
      C.Pi tb e1         -> C.Pi (lowerMeta tb) (go e1)
      C.Set _            -> e
      C.Prop _           -> e
      C.SetN _ _         -> e
      C.ETel tel         -> C.ETel (lowerMeta tel)
      C.Let r ds e1      -> C.Let r (lowerMeta ds) (go e1)
      Paren r e1         -> case go e1 of
        q@(C.QuestionMark _ Nothing) -> q
        e2                           -> Paren r e2
      Absurd _           -> e
      As r n e1          -> As r n (go e1)
      C.Dot r e          -> C.Dot r (go e)
      C.RawApp r es      -> C.RawApp r (lowerMeta es)
      C.OpApp r x es     -> C.OpApp r x (lowerMeta es)
      C.Rec r fs         -> C.Rec r (lowerMeta fs) -- (List.map (id -*- lowerMeta) fs)
      C.RecUpdate r e fs -> C.RecUpdate r (lowerMeta e) (lowerMeta fs) -- (List.map (id -*- lowerMeta) fs)
      C.HiddenArg r e    -> C.HiddenArg r (lowerMeta e)
      C.InstanceArg r e  -> C.InstanceArg r (lowerMeta e)
      C.QuoteGoal r x e  -> C.QuoteGoal r x (lowerMeta e)
      e@C.Quote{}        -> e
      e@C.QuoteTerm{}    -> e
      e@C.Unquote{}      -> e
      C.DontCare e       -> C.DontCare (lowerMeta e)

instance LowerMeta C.Name where
  lowerMeta = id

instance LowerMeta C.QName where
  lowerMeta = id

instance LowerMeta (OpApp C.Expr) where
  lowerMeta (Ordinary e) = Ordinary $ lowerMeta e
  lowerMeta (SyntaxBindingLambda r bs e) = SyntaxBindingLambda r (lowerMeta bs) (lowerMeta e)

instance LowerMeta C.LamBinding where
  lowerMeta b@(C.DomainFree _ _) = b
  lowerMeta (C.DomainFull tb)    = C.DomainFull (lowerMeta tb)

instance LowerMeta C.TypedBindings where
  lowerMeta (C.TypedBindings r bs) = C.TypedBindings r (lowerMeta bs)

instance LowerMeta C.TypedBinding where
  lowerMeta (C.TBind r ns e) = C.TBind r ns (lowerMeta e)
  lowerMeta (C.TNoBind e)    = C.TNoBind (lowerMeta e)

instance LowerMeta C.RHS where
    lowerMeta (C.RHS e)    = C.RHS (lowerMeta e)
    lowerMeta  C.AbsurdRHS = C.AbsurdRHS

instance LowerMeta (Maybe C.Expr) where
    lowerMeta (Just e) = Just (lowerMeta e)
    lowerMeta Nothing  = Nothing

instance LowerMeta C.Declaration where
  lowerMeta = go where
    go d = case d of
      TypeSig rel n e1              -> TypeSig rel n (lowerMeta e1)
      C.Field n e1                  -> C.Field n (lowerMeta e1)
      FunClause lhs rhs whcl        -> FunClause lhs (lowerMeta rhs) (lowerMeta whcl)
      C.DataSig r ind n tel e1      -> C.DataSig r ind n
                                         (lowerMeta tel) (lowerMeta e1)
      Data r ind n tel e1 cs        -> Data r ind n
                                         (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      C.RecordSig r n tel e1        -> C.RecordSig r n
                                         (lowerMeta tel) (lowerMeta e1)
      C.Record r n ind c tel e1 cs  -> C.Record r n ind c
                                         (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      Infix _ _                     -> d
      Syntax _ _                    -> d
      C.PatternSyn _ _ _ _          -> d
      C.Mutual r ds                 -> C.Mutual r (lowerMeta ds)
      Abstract r ds                 -> Abstract r (lowerMeta ds)
      Private r ds                  -> Private r (lowerMeta ds)
      Postulate r sigs              -> Postulate r (lowerMeta sigs)
      C.Primitive r sigs            -> C.Primitive r (lowerMeta sigs)
      C.Open _ _ _                  -> d
      C.Import _ _ _ _ _            -> d
      C.Pragma _                    -> d
      ModuleMacro r n modapp op dir -> ModuleMacro r n
                                         (lowerMeta modapp) op dir
      C.Module r qn tel ds          -> C.Module r qn (lowerMeta tel) (lowerMeta ds)

instance LowerMeta C.ModuleApplication where
  lowerMeta (C.SectionApp r tel e) = C.SectionApp r (lowerMeta tel) (lowerMeta e)
  lowerMeta (C.RecordModuleIFS r rec) = C.RecordModuleIFS r rec

instance LowerMeta C.WhereClause where
  lowerMeta C.NoWhere          = C.NoWhere
  lowerMeta (C.AnyWhere ds)    = C.AnyWhere $ lowerMeta ds
  lowerMeta (C.SomeWhere m ds) = C.SomeWhere m $ lowerMeta ds

instance (LowerMeta a, LowerMeta b) => LowerMeta (a,b) where
  lowerMeta (a, b) = (lowerMeta a, lowerMeta b)

instance LowerMeta a => LowerMeta [a] where
  lowerMeta as = List.map lowerMeta as

instance LowerMeta a => LowerMeta (C.Arg a) where
  lowerMeta aa = fmap lowerMeta aa

instance LowerMeta a => LowerMeta (Named name a) where
  lowerMeta aa = fmap lowerMeta aa
-}

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
  e <- liftIO $ parse exprParser s
  display_info . title =<<
    lift (B.atTopLevel $ prettyA =<< cmd =<< concreteToAbstract_ e)

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
    Nothing                                    -> []
    Just (Pn { srcFile = Nothing })            -> []
    Just (Pn { srcFile = Just f, posPos = p }) ->
       [ Resp_JumpToError (filePath f) p ]
