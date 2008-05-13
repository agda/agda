{-# OPTIONS -fno-cse -cpp -fglasgow-exts -fallow-overlapping-instances #-}

module Interaction.GhciTop
  ( module Interaction.GhciTop
  , module TypeChecker
  , module TM
  , module TypeChecking.MetaVars
  , module TypeChecking.Reduce
  , module TypeChecking.Errors

  , module Syntax.Position
  , module Syntax.Parser
  , module SCo
--  , module SC  -- trivial clash removal: remove all!
--  , module SA
--  , module SI
  , module Syntax.Scope.Base
  , module Syntax.Scope.Monad
  , module Syntax.Translation.ConcreteToAbstract
  , module Syntax.Translation.AbstractToConcrete
  , module Syntax.Translation.InternalToAbstract
  , module Syntax.Abstract.Name

  , module Interaction.Exceptions
  )
  where

import Prelude hiding (print, putStr, putStrLn)
import System.IO hiding (print, putStr, putStrLn)
import System.Directory
import System.IO.Unsafe
import Data.Char
import Data.IORef
import qualified Text.PrettyPrint as P
import Control.Applicative

import Utils.Fresh
import Utils.Monad
import Utils.Monad.Undo
import Utils.IO
import Utils.Pretty
import Utils.String
import Utils.FileName
import Utils.Tuple

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State hiding (State)
import Control.Exception
import Data.List as List
import Data.Map as Map
import System.Exit

import TypeChecker
import TypeChecking.Monad as TM hiding (initState)
import qualified TypeChecking.Monad as TM
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Errors

import Syntax.Position
import Syntax.Parser
import qualified Syntax.Parser.Tokens as T
import Syntax.Concrete as SC
import Syntax.Common as SCo
import Syntax.Concrete.Name as CN
import Syntax.Concrete.Pretty ()
import Syntax.Abstract as SA
import Syntax.Abstract.Pretty
import Syntax.Internal as SI
import Syntax.Scope.Base
import Syntax.Scope.Monad hiding (bindName)
import qualified Syntax.Info as Info
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete hiding (withScope)
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Name

import Interaction.Exceptions
import Interaction.Options
import Interaction.MakeCase
import qualified Interaction.BasicOps as B
import qualified Interaction.CommandLine.CommandLine as CL
import Interaction.Highlighting.Emacs
import Interaction.Highlighting.Generate

import Termination.TermCheck

#include "../undefined.h"

data State = State
  { theTCState   :: TCState
  , theUndoStack :: [TCState]
  , theTopLevel  :: Maybe TopLevelInfo
  }

initState :: State
initState = State
  { theTCState   = TM.initState
  , theUndoStack = []
  , theTopLevel  = Nothing
  }

{-# NOINLINE theState #-}
theState :: IORef State
theState = unsafePerformIO $ newIORef initState

ioTCM :: TCM a -> IO a
ioTCM = ioTCM' Nothing

ioTCM' :: Maybe FilePath
         -- ^ The module being checked (if known).
      -> TCM a -> IO a
ioTCM' mFile cmd = do
  State { theTCState   = st
        , theUndoStack = us
        } <- readIORef theState
  r <- runTCM $ do
      putUndoStack us
      put st
      x <- withEnv initEnv cmd
      st <- get
      us <- getUndoStack
      return (x,st,us)
    `catchError` \err -> do
	s <- prettyError err
        liftIO $ outputErrorInfo mFile (getRange err) s
	liftIO $ display_info "*Error*" s
	fail "exit"
  case r of
    Right (a,st',ss') -> do
      modifyIORef theState $ \s ->
        s { theTCState = st'
          , theUndoStack = ss'
          }
      return a
    Left _ -> exitWith $ ExitFailure 1

-- | Set the current working directory based on the file name of the
-- current module and its module name, so that when the module is
-- imported qualified it will be found.
--
-- The path is assumed to be absolute.
--
-- The given list of declarations should correspond to a module, i.e.
-- it should be non-empty and the last declaration should be
-- 'SC.Module' something.

setWorkingDirectory :: FilePath -> [SC.Declaration] -> IO ()
setWorkingDirectory _    [] = __IMPOSSIBLE__
setWorkingDirectory file xs = case last xs of
  SC.Module _ n _ _ -> setCurrentDirectory (newDir $ countDots n)
  _                 -> __IMPOSSIBLE__
  where
  countDots (SC.QName _)  = 0
  countDots (SC.Qual _ n) = 1 + countDots n

  (path, _, _) = splitFilePath file
  newDir n     = dropDirectory n path

-- | Sets the Agda include directories (corresponding to the -i
-- option).

setIncludeDirectories :: [FilePath] -> TCM ()
setIncludeDirectories is = do
  opts <- commandLineOptions
  setCommandLineOptions (opts { optIncludeDirs = is })

cmd_load :: FilePath -> [FilePath] -> IO ()
cmd_load file includes = infoOnException $ do
    clearSyntaxInfo file
    (pragmas, m) <- parseFile' moduleParser file
    setWorkingDirectory file m
    is <- ioTCM' (Just file) $ do
            enableSyntaxHighlighting
            setIncludeDirectories includes
	    resetState
	    pragmas  <- concat <$> concreteToAbstract_ pragmas	-- identity for top-level pragmas at the moment
            -- Note that pragmas can affect scope checking.
            setOptionsFromPragmas pragmas
	    topLevel <- concreteToAbstract_ (TopLevel m)

            handleError
              -- If there is an error syntax highlighting info can
              -- still be generated.
              (\e -> do generateAndOutputSyntaxInfo
                          file TypeCheckingNotDone topLevel
                        -- The outer error handler tells Emacs to
                        -- reload the syntax highlighting info.
                        throwError e) $ do
              setUndo
              checkDecls $ topLevelDecls topLevel
              setScope $ outsideScope topLevel

              ignoreAbstractMode $
                generateAndOutputSyntaxInfo file TypeCheckingDone topLevel

              -- Do termination checking.
              whenM (optTerminationCheck <$> commandLineOptions) $ do
                errs <- termDecls $ topLevelDecls topLevel
                generateAndOutputTerminationProblemInfo file errs

            -- The module type checked, so let us store the abstract
            -- syntax information. (It could be stored before type
            -- checking, but the functions using it may not work if
            -- the code is not type correct.)
            liftIO $ modifyIORef theState $ \s ->
                       s { theTopLevel = Just topLevel }
	    lispIP

    -- The Emacs mode uses two different annotation mechanisms, and
    -- they cannot be invoked in any order. The one triggered by
    -- adga2-load-action has to be run after the one triggered by
    -- tellEmacsToReloadSyntaxInfo.
    tellEmacsToReloadSyntaxInfo
    putStrLn $ response $ L [A "agda2-load-action", is]
    cmd_metas
  where lispIP  = format . sortRng <$> (tagRng =<< getInteractionPoints)
        tagRng  = mapM (\i -> (,)i <$> getInteractionRange i)
        sortRng = sortBy ((.snd) . compare . snd)
        format  = Q . L . List.map (A . tail . show . fst)

        handleError = flip catchError

cmd_constraints :: IO ()
cmd_constraints = infoOnException $ ioTCM $ do
    cs <- mapM showA =<< B.getConstraints
    liftIO $ display_info "*Constraints*" (unlines cs)


cmd_metas :: IO ()
cmd_metas = infoOnException $ ioTCM $ do -- CL.showMetas []
  ims <- fst <$> B.typeOfMetas B.AsIs
  hms <- snd <$> B.typeOfMetas B.Normalised -- show unsolved implicit arguments normalised
  di <- mapM (\i -> B.withInteractionId (B.outputFormId i) (showA i)) ims
  dh <- mapM showA' hms
  liftIO $ display_info "*All Goals*" $ unlines $
    di ++ dh
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

cmd_undo :: IO ()
cmd_undo = ioTCM undo

cmd_reset :: IO ()
cmd_reset = ioTCM $ do putUndoStack []; resetState

type GoalCommand = InteractionId -> Range -> String -> IO()

cmd_give :: GoalCommand
cmd_give = give_gen B.give $ \s ce -> case ce of (SC.Paren _ _)-> "'paren"
                                                 _             -> "'no-paren"

cmd_refine :: GoalCommand
cmd_refine = give_gen B.refine $ \s -> emacsStr . show

give_gen give_ref mk_newtxt ii rng s = infoOnException $ do
    ioTCM $ do
      prec      <- scopePrecedence <$> getInteractionScope ii
      (ae, iis) <- give_ref ii Nothing =<< B.parseExprIn ii rng s
      newtxt <- A . mk_newtxt s <$> abstractToConcreteCtx prec ae
      let newgs  = Q . L $ List.map showNumIId iis
      liftIO $ putStrLn $ response $
                 L[A"agda2-give-action", showNumIId ii, newtxt, newgs]
    cmd_metas

cmd_context :: B.Rewrite -> GoalCommand
cmd_context norm ii _ _ = infoOnException $ do
  display_info "*Context*" . unlines
      =<< ioTCM (B.withInteractionId ii $ mapM showA =<< B.contextOfMeta ii norm)

cmd_infer :: B.Rewrite -> GoalCommand
cmd_infer norm ii rng s = infoOnException $ do
  display_info "*Inferred Type*"
      =<< ioTCM (B.withInteractionId ii $ showA =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s)

cmd_goal_type :: B.Rewrite -> GoalCommand
cmd_goal_type norm ii _ _ = infoOnException $ do 
    s <- ioTCM $ B.withInteractionId ii $ showA =<< B.typeOfMeta norm ii
    display_info "*Current Goal*" s

-- | Displays the current goal and context.

cmd_goal_type_context :: B.Rewrite -> GoalCommand
cmd_goal_type_context norm ii _ _ = infoOnException $ do 
    goal <- ioTCM $ B.withInteractionId ii $ showA =<< B.typeOfMeta norm ii
    ctx  <- ioTCM (B.withInteractionId ii $ mapM showA =<< B.contextOfMeta ii norm)
    display_info "*Goal and context*"
                 (unlines $ ctx ++ [replicate 40 '-'] ++ lines goal)
  where indent = List.map ("  " ++) . lines

-- | Displays the current goal _and_ infers the type of an expression.

cmd_goal_type_infer :: B.Rewrite -> GoalCommand
cmd_goal_type_infer norm ii rng s = infoOnException $ do 
    goal <- ioTCM $ B.withInteractionId ii $ showA =<< B.typeOfMeta norm ii
    typ  <- ioTCM (B.withInteractionId ii $
                     showA =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s)
    display_info "*Goal and inferred type*"
                 (unlines $
                    ["Want:"] ++
                    indent goal ++
                    ["Have:"] ++
                    indent typ)
  where indent = List.map ("  " ++) . lines

display_info :: String -> String -> IO()
display_info bufname content =
  putStrLn . response
    $ L[A"agda2-info-action", A(quote bufname),  A(quote content)]

response :: Lisp String -> String
response l = show (text "agda2_mode_code" <+> pretty l)

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
                  , keys <$> asks envLetBindings
                  , List.map qnameName . keys . sigDefinitions <$> getSignature
		  ]
  return $ concat [ parts $ nameConcrete x | x <- concat xss]
  where
    parts x = [ s | Id _ s <- nameParts x ]

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

nameModifiers = "" : "'" : "''" : [show i | i <-[3..]]

cmd_make_case :: GoalCommand
cmd_make_case ii rng s = infoOnException $ ioTCM $ do
  cs <- makeCase ii rng s
  B.withInteractionId ii $ do
    pcs <- mapM prettyA cs
    liftIO $ putStrLn $ response $
      L [ A "agda2-make-case-action",
          Q $ L $ List.map (A . quote . show) pcs
        ]

cmd_solveAll :: IO ()
cmd_solveAll = infoOnException $ ioTCM $ do
    out <- getInsts =<< gets stInteractionPoints
    liftIO $ putStrLn $ response $
      L[ A"agda2-solveAll-action" , Q . L $ concatMap prn out]
  where
  getInsts = Map.foldWithKey go (return []) where
    go :: InteractionId -> MetaId -> TCM [(InteractionId, SC.Expr)] -> TCM [(InteractionId, SC.Expr)]
    go ii mi rest = do
      mv <- lookupMeta mi
      withMetaInfo (getMetaInfo mv) $ do    
        args <- getContextArgs
        let out m = do e <- lowerMeta <$> (abstractToConcrete_ =<< reify m)
                       ((ii, e):) <$> rest
        case mvInstantiation mv of InstV{}                        -> out (MetaV mi args)
                                   InstS{}                        -> out (MetaS mi)
                                   TM.Open{}                      -> rest
				   BlockedConst{}                 -> rest
                                   PostponedTypeCheckingProblem{} -> rest
  prn (ii,e)= [showNumIId ii, A $ emacsStr $ show e]

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
      SC.Fun r ae1 e2      -> SC.Fun r (lowerMeta ae1) (go e2)
      SC.Pi tb e1          -> SC.Pi (lowerMeta tb) (go e1)
      SC.Set _             -> e
      SC.Prop _            -> e
      SC.SetN _ _          -> e
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
    lowerMeta (SC.RHS e) = SC.RHS (lowerMeta e)
    lowerMeta  SC.AbsurdRHS = SC.AbsurdRHS

instance LowerMeta SC.Declaration where
  lowerMeta = go where
    go d = case d of
      TypeSig n e1            -> TypeSig n (lowerMeta e1)
      SC.Field n e1           -> SC.Field n (lowerMeta e1)
      FunClause lhs rhs whcl  -> FunClause lhs (lowerMeta rhs) (lowerMeta whcl)
      Data r n tel e1 cs      -> Data r n
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
cmd_compute ignore ii rng s = infoOnException $ do
  d <- ioTCM $ do
    e <- B.parseExprIn ii rng s
    B.withInteractionId ii $ do
      let c = B.evalInCurrent e
      v <- if ignore then ignoreAbstractMode c else c
      prettyA v
  display_info "*Normal Form*" (show d)

-- | Parses and scope checks an expression (using insideScope topLevel
-- as the scope), performs the given command with the expression as
-- input, and displays the result.

parseAndDoAtToplevel
  :: (SA.Expr -> TCM SA.Expr)
     -- ^ The command to perform.
  -> String
     -- ^ The name to used for the buffer displaying the output.
  -> String
     -- ^ The expression to parse.
  -> IO ()
parseAndDoAtToplevel cmd title s = infoOnException $ do
  e <- parse exprParser s
  mTopLevel <- theTopLevel <$> readIORef theState
  display_info title =<< ioTCM (
    case mTopLevel of
      Nothing       -> return "Error: First load the file."
      Just topLevel -> do
        setScope $ insideScope topLevel
        showA =<< cmd =<< concreteToAbstract_ e)

-- | Parse the given expression (as if it were defined at the
-- top-level of the current module) and infer its type.

cmd_infer_toplevel
  :: B.Rewrite  -- ^ Normalise the type?
  -> String
  -> IO ()
cmd_infer_toplevel norm =
  parseAndDoAtToplevel (B.typeInCurrent norm) "*Inferred Type*"

-- | Parse and type check the given expression (as if it were defined
-- at the top-level of the current module) and normalise it.

cmd_compute_toplevel :: Bool -- ^ Ignore abstract?
                     -> String -> IO ()
cmd_compute_toplevel ignore =
  parseAndDoAtToplevel (if ignore then ignoreAbstractMode . c else c)
                       "*Normal Form*"
  where c = B.evalInCurrent

-- change "\<decimal>" to a single character
-- TODO: This seems to be the wrong solution to the problem. Attack
-- the source instead.
emacsStr s = go (show s) where
  go ('\\':ns@(n:_))
     | isDigit n = toEnum (read digits :: Int) : go rest
     where (digits, rest) = span isDigit ns
  go (c:s) = c : go s
  go []    = []


infoOnException m = failOnException inform m where
  inform rng msg = do
    outputErrorInfo Nothing rng msg
    display_info "*Error*" $ unlines [show rng ++ " : ", msg]
    exitWith (ExitFailure 1)

------------------------------------------------------------------------
-- Syntax highlighting

-- | Turns on syntax highlighting for other parts of Agda (notably the
-- import chaser, which sometimes type checks things).

enableSyntaxHighlighting :: TCM ()
enableSyntaxHighlighting = do
  opts <- commandLineOptions
  setCommandLineOptions (opts { optGenerateEmacsFile = True })

-- | Tell the Emacs mode to reload the highlighting information.

tellEmacsToReloadSyntaxInfo :: IO ()
tellEmacsToReloadSyntaxInfo =
  putStrLn $ response $ L [A "agda2-highlight-reload"]

-- | Output syntax highlighting information for the given error
-- (represented as a range and a string), and tell the Emacs mode to
-- reload the highlighting information and go to the first error
-- position.

outputErrorInfo
  :: Maybe FilePath
     -- ^ The file we're working with (if it's known).
  -> Range -> String -> IO ()
outputErrorInfo mFile r s =
  case rStart r of
    NoPos                          -> return ()
    -- Errors for expressions entered using the command line sometimes
    -- have an empty file name component.
    Pn { srcFile = "" }            -> return ()
    Pn { srcFile = f, posPos = p } -> do
      putStrLn $ response $
        L [A "annotation-goto", Q $ L [A (show f), A ".", A (show p)]]
      when (mFile /= Just f) $ clearSyntaxInfo f
      appendSyntaxInfo f $ generateErrorInfo r s
      tellEmacsToReloadSyntaxInfo

------------------------------------------------------------------------
-- Implicit arguments

-- | Tells Agda whether or not to show implicit arguments.

showImplicitArgs :: Bool -- ^ Show them?
                 -> IO ()
showImplicitArgs showImpl = ioTCM $ do
  opts <- commandLineOptions
  setCommandLineOptions (opts { optShowImplicit = showImpl })

-- | Toggle display of implicit arguments.

toggleImplicitArgs :: IO ()
toggleImplicitArgs = ioTCM $ do
  opts <- commandLineOptions
  setCommandLineOptions (opts { optShowImplicit =
                                  not $ optShowImplicit opts })
