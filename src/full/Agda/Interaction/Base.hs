{-# OPTIONS_GHC -fno-cse #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Interaction.Base where

import           Control.Concurrent.STM.TChan
import           Control.Concurrent.STM.TVar
import           Control.Monad.Identity
import           Control.Monad.State

import qualified Data.List                    as List
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import           Data.Maybe                   (listToMaybe)

import {-# SOURCE #-} Agda.TypeChecking.Monad.Base
  (HighlightingLevel, HighlightingMethod, TCM, ProblemId, Comparison, Polarity)

import           Agda.Syntax.Abstract         (QName)
import           Agda.Syntax.Common           (InteractionId (..))
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base       (ScopeInfo)

import           Agda.Interaction.Options     (CommandLineOptions,
                                               defaultOptions)

import           Agda.Utils.Except            (ExceptT, MonadError (throwError),
                                               runExceptT)
import           Agda.Utils.FileName          (AbsolutePath, mkAbsolute)
import           Agda.Utils.Time              (ClockTime)

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
  , optionsOnReload      :: CommandLineOptions
    -- ^ Reset the options on each reload to these.
  , oldInteractionScopes :: !OldInteractionScopes
    -- ^ We remember (the scope of) old interaction points to make it
    --   possible to parse and compute highlighting information for the
    --   expression that it got replaced by.
  , commandQueue         :: !CommandQueue
    -- ^ The command queue.
    --
    -- This queue should only be manipulated by
    -- 'initialiseCommandQueue' and 'maybeAbort'.
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


------------------------------------------------------------------------
-- Command queues

-- | A generalised command type.

data Command' a
  = Command !a
    -- ^ A command.
  | Done
    -- ^ Stop processing commands.
  | Error String
    -- ^ An error message for a command that could not be parsed.
  deriving Show

-- | IOTCM commands.

type Command = Command' IOTCM

-- | Command queues.

data CommandQueue = CommandQueue
  { commands :: !(TChan (Integer, Command))
    -- ^ Commands that should be processed, in the order in which they
    -- should be processed. Each command is associated with a number,
    -- and the numbers are strictly increasing. Abort commands are not
    -- put on this queue.
  , abort    :: !(TVar (Maybe Integer))
    -- ^ When this variable is set to @Just n@ an attempt is made to
    -- abort all commands with a command number that is at most @n@.
  }


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

    -- | Shows all the top-level names in the given module, along with
    -- their types. Uses the top-level scope.
  | Cmd_show_module_contents_toplevel
                        Rewrite
                        String

    -- | Shows all the top-level names in scope which mention all the given
    -- identifiers in their type.
  | Cmd_search_about_toplevel Rewrite String

    -- | Solve (all goals / the goal at point) whose values are determined by
    -- the constraints.
  | Cmd_solveAll Rewrite
  | Cmd_solveOne Rewrite InteractionId range String

    -- | Solve (all goals / the goal at point) by using Auto.
  | Cmd_autoOne            InteractionId range String
  | Cmd_autoAll

    -- | Parse the given expression (as if it were defined at the
    -- top-level of the current module) and infer its type.
  | Cmd_infer_toplevel  Rewrite  -- Normalise the type?
                        String


    -- | Parse and type check the given expression (as if it were defined
    -- at the top-level of the current module) and normalise it.
  | Cmd_compute_toplevel ComputeMode
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
  | Cmd_load_highlighting_info FilePath

    -- | Tells Agda to compute token-based highlighting information
    -- for the file.
    --
    -- This command works even if the file's module name does not
    -- match its location in the file system, or if the file is not
    -- scope-correct. Furthermore no file names are put in the
    -- generated output. Thus it is fine to put source code into a
    -- temporary file before calling this command. However, the file
    -- extension should be correct.
    --
    -- If the second argument is 'Remove', then the (presumably
    -- temporary) file is removed after it has been read.
  | Cmd_tokenHighlighting FilePath Remove

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

  | Cmd_give            UseForce InteractionId range String

  | Cmd_refine          InteractionId range String

  | Cmd_intro           Bool InteractionId range String

  | Cmd_refine_or_intro Bool InteractionId range String

  | Cmd_context         Rewrite InteractionId range String

  | Cmd_helper_function Rewrite InteractionId range String

  | Cmd_infer           Rewrite InteractionId range String

  | Cmd_goal_type       Rewrite InteractionId range String

  -- | Grabs the current goal's type and checks the expression in the hole
  -- against it. Returns the elaborated term.
  | Cmd_elaborate_give
                        Rewrite InteractionId range String

    -- | Displays the current goal and context.
  | Cmd_goal_type_context Rewrite InteractionId range String

    -- | Displays the current goal and context /and/ infers the type of an
    -- expression.
  | Cmd_goal_type_context_infer
                        Rewrite InteractionId range String

  -- | Grabs the current goal's type and checks the expression in the hole
  -- against it.
  | Cmd_goal_type_context_check
                        Rewrite InteractionId range String

    -- | Shows all the top-level names in the given module, along with
    -- their types. Uses the scope of the given goal.
  | Cmd_show_module_contents
                        Rewrite InteractionId range String

  | Cmd_make_case       InteractionId range String

  | Cmd_compute         ComputeMode
                        InteractionId range String

  | Cmd_why_in_scope    InteractionId range String
  | Cmd_why_in_scope_toplevel String
    -- | Displays version of the running Agda
  | Cmd_show_version
  | Cmd_abort
    -- ^ Abort the current computation.
    --
    -- Does nothing if no computation is in progress.
  | Cmd_exit
    -- ^ Exit the program.
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

-- | Used to indicate whether something should be removed or not.

data Remove
  = Remove
  | Keep
  deriving (Show, Read)




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
  _            -> []

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

data Rewrite =  AsIs | Instantiated | HeadNormal | Simplified | Normalised
    deriving (Show, Read)

data ComputeMode = DefaultCompute | IgnoreAbstract | UseShowInstance
  deriving (Show, Read, Eq)

data UseForce
  = WithForce     -- ^ Ignore additional checks, like termination/positivity...
  | WithoutForce  -- ^ Don't ignore any checks.
  deriving (Eq, Read, Show)

data OutputForm a b = OutputForm Range [ProblemId] (OutputConstraint a b)
  deriving (Functor)

data OutputConstraint a b
      = OfType b a | CmpInType Comparison a b b
                   | CmpElim [Polarity] a [b] [b]
      | JustType b | CmpTypes Comparison b b
                   | CmpLevels Comparison b b
                   | CmpTeles Comparison b b
      | JustSort b | CmpSorts Comparison b b
      | Guard (OutputConstraint a b) ProblemId
      | Assign b a | TypedAssign b a a | PostponedCheckArgs b [a] a a
      | IsEmptyType a
      | SizeLtSat a
      | FindInstanceOF b a [(a,a,a)]
      | PTSInstance b b
      | PostponedCheckFunDef QName a
  deriving (Functor)

-- | A subset of 'OutputConstraint'.

data OutputConstraint' a b = OfType'
  { ofName :: b
  , ofExpr :: a
  }

data OutputContextEntry name ty val
  = ContextVar name ty
  | ContextLet name ty val
