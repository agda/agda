{-# LANGUAGE CPP, TypeSynonymInstances #-}
{-# OPTIONS -fno-cse #-}

module Agda.Interaction.GhciTop
  ( module Agda.Interaction.GhciTop
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
import System.IO.Unsafe
import Data.Char
import Data.Maybe
import Data.IORef
import Data.Function
import Control.Applicative
import qualified System.IO.UTF8 as UTF8

import Agda.Utils.Fresh
import Agda.Utils.Monad
import Agda.Utils.Monad.Undo
import Agda.Utils.Pretty as P
import Agda.Utils.String
import Agda.Utils.FileName
import Agda.Utils.Tuple

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State hiding (State)
import Control.Exception
import Data.List as List
import qualified Data.Map as Map
import System.Exit
import qualified System.Mem as System
import System.Time

import Agda.TypeChecker
import Agda.TypeChecking.Monad as TM
  hiding (initState, setCommandLineOptions)
import qualified Agda.TypeChecking.Monad as TM
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Serialise (encodeFile)

import Agda.Syntax.Position
import Agda.Syntax.Parser
import qualified Agda.Syntax.Parser.Tokens as T
import Agda.Syntax.Concrete as SC
import Agda.Syntax.Common as SCo
import Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract as SA
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Internal as SI
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding (bindName, withCurrentModule)
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete hiding (withScope)
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Name

import Agda.Interaction.Exceptions
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.MakeCase
import qualified Agda.Interaction.BasicOps as B
import qualified Agda.Interaction.CommandLine.CommandLine as CL
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Generate
import qualified Agda.Interaction.Imports as Imp

import Agda.Termination.TermCheck

import qualified Agda.Compiler.MAlonzo.Compiler as MAlonzo

#include "../undefined.h"
import Agda.Utils.Impossible

data State = State
  { theTCState           :: TCState
  , theUndoStack         :: [TCState]
  , theInteractionPoints :: [InteractionId]
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
  }

initState :: State
initState = State
  { theTCState           = TM.initState
  , theUndoStack         = []
  , theInteractionPoints = []
  , theCurrentFile       = Nothing
  }

{-# NOINLINE theState #-}
theState :: IORef State
theState = unsafePerformIO $ newIORef initState

-- | An interactive computation.

data Interaction = Interaction
  { isIndependent :: Bool
    -- ^ Can the command run even if the relevant file has not been
    -- loaded into the state?
  , command :: TCM (Maybe ModuleName)
    -- ^ If a module name is returned, then syntax highlighting
    -- information will be written for the given module (by 'ioTCM').
  }

-- | Runs a 'TCM' computation. All calls from the Emacs mode should be
-- wrapped in this function.

ioTCM :: FilePath
         -- ^ The current file. If this file does not match
         -- 'theCurrentFile', and the 'Interaction' is not
         -- \"independent\", then an error is raised.
      -> Maybe FilePath
         -- ^ Syntax highlighting information will be written to this
         -- file, if any.
      -> Interaction
      -> IO ()
ioTCM current highlightingFile cmd = infoOnException $ do
  current <- absolute current

  -- Read the state.
  State { theTCState     = st
        , theUndoStack   = us
        , theCurrentFile = f
        } <- readIORef theState

  -- Run the computation.
  r <- if not (isIndependent cmd) && Just current /= (fst <$> f) then
         let s = "Error: First load the file." in
         return $ Right $ Left (s, TCErr Nothing $ Exception noRange s)
        else
         runTCM $ catchError (do
             putUndoStack us
             put st
             x  <- withEnv initEnv $ command cmd
             st <- get
             us <- getUndoStack
             return (Right (x, st, us))
           ) (\e -> do
             s <- prettyError e
             return (Left (s, e))
           )

  -- Update the state.
  case r of
    Right (Right (m, st', us')) ->
      modifyIORef theState $ \s ->
        s { theTCState   = st'
          , theUndoStack = us'
          }
    _ | isIndependent cmd ->
      modifyIORef theState $ \s ->
        s { theCurrentFile = Nothing }
    _ -> return ()

  -- Write out syntax highlighting info.
  case highlightingFile of
    Nothing -> return ()
    Just f  -> do
      let errHi e s = errHighlighting e
                        `mplus`
                      ((\h -> (h, Map.empty)) <$>
                           generateErrorInfo (getRange e) s)
      UTF8.writeFile f $
        showHighlightingInfo $
          case r of
            Right (Right (mm, st', _)) -> do
              m  <- mm
              mi <- Map.lookup (SA.toTopLevelModuleName m)
                               (stVisitedModules st')
              return ( iHighlighting $ miInterface mi
                     , stModuleToSource st'
                     )
            Right (Left (s, e)) -> errHi e (Just s)
            Left e              -> errHi e Nothing

  -- If an error was encountered, display an error message and exit
  -- with an error code.
  case r of
    Right (Right _)     -> return ()
    Right (Left (s, e)) -> displayErrorAndExit (getRange e) s
    Left e              -> displayErrorAndExit (getRange e) $
                             tcErrString e

-- | @cmd_load m includes@ loads the module in file @m@, using
-- @includes@ as the include directories.

cmd_load :: FilePath -> [FilePath] -> Interaction
cmd_load m includes =
  cmd_load' m includes True (\_ -> command cmd_metas >> return ())

-- | @cmd_load' m includes cmd cmd2@ loads the module in file @m@,
-- using @includes@ as the include directories.
--
-- If type checking completes without any exceptions having been
-- encountered then the command @cmd r@ is executed, where @r@ is the
-- result of 'Imp.typeCheck'.

cmd_load' :: FilePath -> [FilePath]
          -> Bool -- ^ Allow unsolved meta-variables?
          -> ((Interface, Maybe Imp.Warnings) -> TCM ())
          -> Interaction
cmd_load' file includes unsolvedOK cmd = Interaction True $ do
  clearUndoHistory

  -- Forget the previous "current file" and interaction points.
  liftIO $ modifyIORef theState $ \s ->
    s { theInteractionPoints = []
      , theCurrentFile       = Nothing
      }

  f <- liftIO $ absolute file
  t <- liftIO $ getModificationTime file

  -- All options are reset when a file is reloaded, including the
  -- choice of whether or not to display implicit arguments.
  oldIncs <- getIncludeDirs
  setCommandLineOptions $
    defaultOptions { optAllowUnsolved = unsolvedOK
                   , optIncludeDirs   = includes
                   }

  -- Reset the state, preserving options and decoded modules. Note
  -- that Imp.typeCheck resets the decoded modules if the include
  -- directories have changed.
  preserveDecodedModules resetState
  setUndo

  ok <- Imp.typeCheck file Imp.ProjectRoot (Just oldIncs)

  -- The module type checked. If the file was not changed while the
  -- type checker was running then the interaction points and the
  -- "current file" are stored.
  t' <- liftIO $ getModificationTime file
  when (t == t') $ do
    is <- sortInteractionPoints =<< getInteractionPoints
    liftIO $ modifyIORef theState $ \s ->
      s { theInteractionPoints = is
        , theCurrentFile       = Just (f, t)
        }

  cmd ok

  liftIO System.performGC

  return $ Just $ iModuleName (fst ok)

-- | @cmd_compile m includes@ compiles the module in file @m@, using
-- @includes@ as the include directories.

cmd_compile :: FilePath -> [FilePath] -> Interaction
cmd_compile file includes =
  cmd_load' file includes False (\(i, mw) ->
    case mw of
      Nothing -> do
        MAlonzo.compilerMain i
        display_info "*Compilation result*"
                   "The module was successfully compiled."
      Just w ->
        display_info errorTitle $ unlines
          [ "You can only compile modules without unsolved metavariables"
          , "or termination checking problems."
          ])

cmd_constraints :: Interaction
cmd_constraints = Interaction False $ do
    cs <- map show <$> B.getConstraints
    display_info "*Constraints*" (unlines cs)
    return Nothing

cmd_metas :: Interaction
cmd_metas = Interaction False $ do -- CL.showMetas []
  ims <- fst <$> B.typeOfMetas B.AsIs
  hms <- snd <$> B.typeOfMetas B.Normalised -- show unsolved implicit arguments normalised
  di <- mapM (\i -> B.withInteractionId (B.outputFormId i) (showA i)) ims
  dh <- mapM showA' hms
  display_info "*All Goals*" $ unlines $ di ++ dh
  return Nothing
  where
    metaId (B.OfType i _) = i
    metaId (B.JustType i) = i
    metaId (B.JustSort i) = i
    metaId (B.Assign i e) = i
    metaId _ = __IMPOSSIBLE__
    showA' m = do
      r <- getMetaRange (metaId m)
      d <- B.withMetaId (B.outputFormId m) (showA m)
      return $ d ++ "  [ at " ++ show r ++ " ]"

cmd_undo :: Interaction
cmd_undo = Interaction False $ do
  undo
  return Nothing

cmd_reset :: Interaction
cmd_reset = Interaction True $ do
  putUndoStack []
  preserveDecodedModules resetState
  return Nothing

type GoalCommand = InteractionId -> Range -> String -> Interaction

cmd_give :: GoalCommand
cmd_give = give_gen B.give $ \s ce -> case ce of (SC.Paren _ _)-> "'paren"
                                                 _             -> "'no-paren"

cmd_refine :: GoalCommand
cmd_refine = give_gen B.refine $ \s -> quote . show

give_gen give_ref mk_newtxt ii rng s = Interaction False $ do
  scope     <- getInteractionScope ii
  (ae, iis) <- give_ref ii Nothing =<< B.parseExprIn ii rng s
  let newtxt = A . mk_newtxt s $ abstractToConcrete (makeEnv scope) ae
  iis       <- sortInteractionPoints iis
  liftIO $ modifyIORef theState $ \s ->
             s { theInteractionPoints =
                   replace ii iis (theInteractionPoints s) }
  liftIO $ UTF8.putStrLn $ response $
             L [A "agda2-give-action", showNumIId ii, newtxt]
  command cmd_metas
  return Nothing
  where
  -- Substitutes xs for x in ys.
  replace x xs ys = concatMap (\y -> if y == x then xs else [y]) ys

-- | Sorts interaction points based on their ranges.

sortInteractionPoints :: [InteractionId] -> TCM [InteractionId]
sortInteractionPoints is =
  map fst . sortBy (compare `on` snd) <$>
    mapM (\i -> (,) i <$> getInteractionRange i) is

-- | Pretty-prints the type of the meta-variable.

prettyTypeOfMeta :: B.Rewrite -> InteractionId -> TCM Doc
prettyTypeOfMeta norm ii = do
  form <- B.typeOfMeta norm ii
  case form of
    B.OfType _ e -> prettyA e
    _            -> text <$> showA form

-- | Pretty-prints the context of the given meta-variable.

prettyContext
  :: B.Rewrite      -- ^ Normalise?
  -> InteractionId
  -> TCM Doc
prettyContext norm ii = B.withInteractionId ii $ do
  ctx <- B.contextOfMeta ii norm
  es  <- mapM (prettyA . B.ofExpr) ctx
  ns  <- mapM (showA   . B.ofName) ctx
  let maxLen = maximum $ 0 : filter (< longNameLength) (map length ns)
  return $ vcat $
           map (\(n, e) -> text n $$ nest (maxLen + 1) (text ":") <+> e) $
           zip ns es

-- | 'prettyContext' lays out @n : e@ on (at least) two lines if @n@
-- has at least @longNameLength@ characters.

longNameLength = 10

cmd_context :: B.Rewrite -> GoalCommand
cmd_context norm ii _ _ = Interaction False $ do
  display_infoD "*Context*" =<< prettyContext norm ii
  return Nothing

cmd_infer :: B.Rewrite -> GoalCommand
cmd_infer norm ii rng s = Interaction False $ do
  display_infoD "*Inferred Type*"
    =<< B.withInteractionId ii
          (prettyA =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s)
  return Nothing

cmd_goal_type :: B.Rewrite -> GoalCommand
cmd_goal_type norm ii _ _ = Interaction False $ do
  s <- B.withInteractionId ii $ prettyTypeOfMeta norm ii
  display_infoD "*Current Goal*" s
  return Nothing

-- | Displays the current goal and context plus the given document.

cmd_goal_type_context_and doc norm ii _ _ = do
  goal <- B.withInteractionId ii $ prettyTypeOfMeta norm ii
  ctx  <- prettyContext norm ii
  display_infoD "*Goal type etc.*"
                (ctx $+$
                 text (replicate 60 '\x2014') $+$
                 text "Goal:" <+> goal $+$
                 doc)
  return Nothing

-- | Displays the current goal and context.

cmd_goal_type_context :: B.Rewrite -> GoalCommand
cmd_goal_type_context norm ii rng s = Interaction False $
  cmd_goal_type_context_and P.empty norm ii rng s

-- | Displays the current goal and context /and/ infers the type of an
-- expression.

cmd_goal_type_context_infer :: B.Rewrite -> GoalCommand
cmd_goal_type_context_infer norm ii rng s = Interaction False $ do
  typ <- B.withInteractionId ii $
           prettyA =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s
  cmd_goal_type_context_and (text "Have:" <+> typ) norm ii rng s

-- | Sets the command line options and updates the status information.

setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts = do
  TM.setCommandLineOptions PersistentOptions opts
  displayStatus

-- | Displays\/updates some status information (currently just
-- indicates whether or not implicit arguments are shown).

displayStatus :: TCM ()
displayStatus = do
  showImpl <- ifM showImplicitArguments
                  (return $ Just "ShowImplicit")
                  (return Nothing)

  -- Check if the file was successfully type checked, and has not
  -- changed since. Note: This code does not check if any dependencies
  -- have changed, and uses a time stamp to check for changes.
  cur      <- theCurrentFile <$> liftIO (readIORef theState)
  checked  <- case cur of
    Nothing     -> return Nothing
    Just (f, t) -> do
      t' <- liftIO $ getModificationTime $ filePath f
      case t == t' of
        False -> return Nothing
        True  -> do
          w <- miWarnings . maybe __IMPOSSIBLE__ id <$>
                 (getVisitedModule =<<
                    maybe __IMPOSSIBLE__ id .
                      Map.lookup f <$> sourceToModule)
          return $ if w then Nothing else Just "Checked"

  let statusString = intercalate "," $ catMaybes [checked, showImpl]

  liftIO $ UTF8.putStrLn $ response $
    L [A "agda2-status-action", A (quote statusString)]

-- | @display_info' header content@ displays @content@ (with header
-- @header@) in some suitable way.

display_info' :: String -> String -> IO ()
display_info' bufname content =
  UTF8.putStrLn $ response $
    L [ A "agda2-info-action"
      , A (quote bufname)
      , A (quote content)
      ]

-- | @display_info@ does what @display_info'@ does, but additionally
-- displays some status information (see 'displayStatus').

display_info :: String -> String -> TCM ()
display_info bufname content = do
  displayStatus
  liftIO $ display_info' bufname content

-- | Like 'display_info', but takes a 'Doc' instead of a 'String'.

display_infoD :: String -> Doc -> TCM ()
display_infoD bufname content = display_info bufname (render content)

-- | Formats a response command.

response :: Lisp String -> String
response l = show (text "agda2_mode_code" <+> pretty l)

-- | Formats a response string.

responseString :: Lisp String -> String
responseString s = response $
  L [A "setq", A "agda2-response", s]

-- | Responds to a query.

respond :: Lisp String -> IO ()
respond = UTF8.putStrLn . responseString

data Lisp a = A a | L [Lisp a] | Q (Lisp a)

instance Pretty a => Pretty (Lisp a) where
  pretty (A a ) = pretty a
  pretty (L xs) = parens (sep (List.map pretty xs))
  pretty (Q x)  = text "'"<>pretty x

instance Pretty String where pretty = text

instance Pretty a => Show (Lisp a) where show = show . pretty

showNumIId = A . tail . show

takenNameStr :: TCM [String]
takenNameStr = do
  xss <- sequence [ List.map (fst . unArg) <$> getContext
                  , Map.keys <$> asks envLetBindings
                  , List.map qnameName . Map.keys . sigDefinitions <$> getSignature
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

cmd_make_case :: GoalCommand
cmd_make_case ii rng s = Interaction False $ do
  cs <- makeCase ii rng s
  B.withInteractionId ii $ do
    pcs <- mapM prettyA cs
    liftIO $ UTF8.putStrLn $ response $
      L [ A "agda2-make-case-action",
          Q $ L $ List.map (A . quote . show) pcs
        ]
  return Nothing

cmd_solveAll :: Interaction
cmd_solveAll = Interaction False $ do
  out <- getInsts
  liftIO $ UTF8.putStrLn $ response $
    L[ A"agda2-solveAll-action" , Q . L $ concatMap prn out]
  return Nothing
  where
  getInsts = mapM lowr =<< B.getSolvedInteractionPoints
    where
      lowr (i, m, e) = do
        mi <- getMetaInfo <$> lookupMeta m
        e <- withMetaInfo mi $ lowerMeta <$> abstractToConcrete_ e
        return (i, e)
  prn (ii,e)= [showNumIId ii, A $ quote $ show e]

class LowerMeta a where lowerMeta :: a -> a
instance LowerMeta SC.Expr where
  lowerMeta = go where
    go e = case e of
      Ident _              -> e
      SC.Lit _             -> e
      SC.QuestionMark _ _  -> preMeta
      SC.Underscore _ _    -> preUscore
      SC.App r e1 ae2      -> case appView e of
        SC.AppView (SC.QuestionMark _ _) _ -> preMeta
        SC.AppView (SC.Underscore   _ _) _ -> preUscore
        _ -> SC.App r (go e1) (lowerMeta ae2)
      SC.WithApp r e es	   -> SC.WithApp r (lowerMeta e) (lowerMeta es)
      SC.Lam r bs e1       -> SC.Lam r (lowerMeta bs) (go e1)
      SC.AbsurdLam r h     -> SC.AbsurdLam r h
      SC.Fun r ae1 e2      -> SC.Fun r (lowerMeta ae1) (go e2)
      SC.Pi tb e1          -> SC.Pi (lowerMeta tb) (go e1)
      SC.Set _             -> e
      SC.Prop _            -> e
      SC.SetN _ _          -> e
      SC.ETel tel          -> SC.ETel (lowerMeta tel)
      SC.Let r ds e1       -> SC.Let r (lowerMeta ds) (go e1)
      Paren r e1           -> case go e1 of
        q@(SC.QuestionMark _ Nothing) -> q
        e2                            -> Paren r e2
      Absurd _          -> e
      As r n e1         -> As r n (go e1)
      SC.Dot r e	-> SC.Dot r (go e)
      SC.RawApp r es	-> SC.RawApp r (lowerMeta es)
      SC.OpApp r x es	-> SC.OpApp r x (lowerMeta es)
      SC.Rec r fs	-> SC.Rec r (List.map (id -*- lowerMeta) fs)
      SC.HiddenArg r e	-> SC.HiddenArg r (lowerMeta e)

instance LowerMeta SC.LamBinding where
  lowerMeta b@(SC.DomainFree _ _) = b
  lowerMeta (SC.DomainFull tb)    = SC.DomainFull (lowerMeta tb)

instance LowerMeta SC.TypedBindings where
  lowerMeta (SC.TypedBindings r h bs) = SC.TypedBindings r h (lowerMeta bs)

instance LowerMeta SC.TypedBinding where
  lowerMeta (SC.TBind r ns e) = SC.TBind r ns (lowerMeta e)
  lowerMeta (SC.TNoBind e)    = SC.TNoBind (lowerMeta e)

instance LowerMeta SC.RHS where
    lowerMeta (SC.RHS e)    = SC.RHS (lowerMeta e)
    lowerMeta  SC.AbsurdRHS = SC.AbsurdRHS

instance LowerMeta SC.Declaration where
  lowerMeta = go where
    go d = case d of
      TypeSig n e1            -> TypeSig n (lowerMeta e1)
      SC.Field n e1           -> SC.Field n (lowerMeta e1)
      FunClause lhs rhs whcl  -> FunClause lhs (lowerMeta rhs) (lowerMeta whcl)
      Data r ind n tel e1 cs  -> Data r ind n
                                 (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      SC.Record r n tel e1 cs -> SC.Record r n
                                 (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      Infix _ _               -> d
      Mutual r ds             -> Mutual r (lowerMeta ds)
      Abstract r ds           -> Abstract r (lowerMeta ds)
      Private r ds            -> Private r (lowerMeta ds)
      Postulate r sigs        -> Postulate r (lowerMeta sigs)
      SC.Primitive r sigs     -> SC.Primitive r (lowerMeta sigs)
      SC.Open _ _ _           -> d
      SC.Import _ _ _ _ _     -> d
      SC.Pragma _	      -> d
      ModuleMacro r n tel e1 op dir -> ModuleMacro r n
                                    (lowerMeta tel) (lowerMeta e1) op dir
      SC.Module r qn tel ds   -> SC.Module r qn (lowerMeta tel) (lowerMeta ds)

instance LowerMeta SC.WhereClause where
  lowerMeta SC.NoWhere		= SC.NoWhere
  lowerMeta (SC.AnyWhere ds)	= SC.AnyWhere $ lowerMeta ds
  lowerMeta (SC.SomeWhere m ds) = SC.SomeWhere m $ lowerMeta ds

instance LowerMeta a => LowerMeta [a] where
  lowerMeta as = List.map lowerMeta as

instance LowerMeta a => LowerMeta (Arg a) where
  lowerMeta aa = fmap lowerMeta aa

instance LowerMeta a => LowerMeta (Named name a) where
  lowerMeta aa = fmap lowerMeta aa


preMeta   = SC.QuestionMark noRange Nothing
preUscore = SC.Underscore   noRange Nothing

cmd_compute :: Bool -- ^ Ignore abstract?
               -> GoalCommand
cmd_compute ignore ii rng s = Interaction False $ do
  e <- B.parseExprIn ii rng s
  d <- B.withInteractionId ii $ do
         let c = B.evalInCurrent e
         v <- if ignore then ignoreAbstractMode c else c
         prettyA v
  display_info "*Normal Form*" (show d)
  return Nothing

-- | Parses and scope checks an expression (using the \"inside scope\"
-- as the scope), performs the given command with the expression as
-- input, and displays the result.

parseAndDoAtToplevel
  :: (SA.Expr -> TCM SA.Expr)
     -- ^ The command to perform.
  -> String
     -- ^ The name to used for the buffer displaying the output.
  -> String
     -- ^ The expression to parse.
  -> Interaction
parseAndDoAtToplevel cmd title s = Interaction False $ do
  e <- liftIO $ parse exprParser s
  display_info title =<< do
    mCurrent <- stCurrentModule <$> get
    case mCurrent of
      Nothing      -> return "Error: First load the file."
      Just current -> do
        r <- getVisitedModule (SA.toTopLevelModuleName current)
        case r of
          Nothing -> __IMPOSSIBLE__
          Just mi -> do
            setScope $ iInsideScope $ miInterface mi
            showA =<< cmd =<< concreteToAbstract_ e
  return Nothing

-- | Parse the given expression (as if it were defined at the
-- top-level of the current module) and infer its type.

cmd_infer_toplevel
  :: B.Rewrite  -- ^ Normalise the type?
  -> String
  -> Interaction
cmd_infer_toplevel norm =
  parseAndDoAtToplevel (B.typeInCurrent norm) "*Inferred Type*"

-- | Parse and type check the given expression (as if it were defined
-- at the top-level of the current module) and normalise it.

cmd_compute_toplevel :: Bool -- ^ Ignore abstract?
                     -> String -> Interaction
cmd_compute_toplevel ignore =
  parseAndDoAtToplevel (if ignore then ignoreAbstractMode . c else c)
                       "*Normal Form*"
  where c = B.evalInCurrent

------------------------------------------------------------------------
-- Syntax highlighting

-- | @cmd_write_highlighting_info source target@ writes syntax
-- highlighting information for the module in @source@ into @target@.
-- If the module does not exist, or its module name is malformed or
-- cannot be determined, or the module has not already been visited,
-- or the cached info is out of date, then the representation of \"no
-- highlighting information available\" is instead written to
-- @target@.

cmd_write_highlighting_info :: FilePath -> FilePath -> Interaction
cmd_write_highlighting_info source target = Interaction True $ do
  liftIO . UTF8.writeFile target . showHighlightingInfo =<< do
    ex <- liftIO $ doesFileExist source
    case ex of
      False -> return Nothing
      True  -> do
        mmi <- (getVisitedModule =<< Imp.moduleName source)
                 `catchError`
               \_ -> return Nothing
        case mmi of
          Nothing     -> return Nothing
          Just mi -> do
            sourceT <- liftIO $ getModificationTime source
            if sourceT <= miTimeStamp mi
             then do
              modFile <- stModuleToSource <$> get
              return $ Just (iHighlighting $ miInterface mi, modFile)
             else
              return Nothing
  return Nothing

-- | Returns the interaction ids for all goals in the current module,
-- in the order in which they appear in the module. If there is no
-- current module, then an empty list of goals is returned.

cmd_goals :: FilePath
             -- ^ If the module name in this file does not match that
             -- of the current module (or the module name cannot be
             -- determined), then an empty list of goals is returned.
          -> Interaction
cmd_goals f = Interaction True $ do
  is <- do
    ex <- liftIO $ doesFileExist f
    case ex of
      False -> return []
      True  -> do
        mm       <- (Just <$> Imp.moduleName f)
                      `catchError`
                    \_ -> return Nothing
        mCurrent <- stCurrentModule <$> get
        if mm == (SA.toTopLevelModuleName <$> mCurrent) then
          theInteractionPoints <$> liftIO (readIORef theState)
         else
          return []
  liftIO $ respond $ Q $ L $ List.map showNumIId is
  return Nothing

-- | Tells the Emacs mode to go to the first error position (if any).

tellEmacsToJumpToError :: Range -> IO ()
tellEmacsToJumpToError r = do
  case rStart r of
    Nothing                                    -> return ()
    Just (Pn { srcFile = Nothing })            -> return ()
    Just (Pn { srcFile = Just f, posPos = p }) ->
      UTF8.putStrLn $ response $
        L [ A "annotation-goto"
          , Q $ L [A (quote $ filePath f), A ".", A (show p)]
          ]

------------------------------------------------------------------------
-- Implicit arguments

-- | Tells Agda whether or not to show implicit arguments.

showImplicitArgs :: Bool -- ^ Show them?
                 -> Interaction
showImplicitArgs showImpl = Interaction False $ do
  opts <- commandLineOptions
  setCommandLineOptions (opts { optShowImplicit = showImpl })
  return Nothing

-- | Toggle display of implicit arguments.

toggleImplicitArgs :: Interaction
toggleImplicitArgs = Interaction False $ do
  opts <- commandLineOptions
  setCommandLineOptions (opts { optShowImplicit =
                                  not $ optShowImplicit opts })
  return Nothing

------------------------------------------------------------------------
-- Error handling

-- | When an error message is displayed the following title should be
-- used, if appropriate.

errorTitle :: String
errorTitle = "*Error*"

-- | Displays an error, instructs Emacs to jump to the site of the
-- error, and terminates the program.

displayErrorAndExit :: Range -> String -> IO a
displayErrorAndExit r s = do
  display_info' errorTitle s
  tellEmacsToJumpToError r
  exitWith (ExitFailure 1)

-- | Outermost error handler.

infoOnException m =
  failOnException displayErrorAndExit m `catchImpossible` \e ->
    displayErrorAndExit noRange (show e)
