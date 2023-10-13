{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Common where

import Prelude hiding ((!!))

import Data.List (sortBy, isPrefixOf)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap
import Data.Char
import Data.Function (on)

import Control.Monad
import Control.Monad.State

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.TopLevelModuleName

import Agda.Interaction.FindFile ( srcFilePath )
import Agda.Interaction.Options
import Agda.Interaction.Imports  ( CheckResult, crInterface, crSource, Source(..) )
import Agda.Interaction.Library

import Agda.TypeChecking.Monad as TCM

import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1          ( pattern (:|) )
import Agda.Utils.Maybe
import Agda.Utils.WithDefault    ( lensCollapseDefault )

import Agda.Utils.Impossible

data IsMain = IsMain | NotMain
  deriving (Eq, Show)

-- | Conjunctive semigroup ('NotMain' is absorbing).
instance Semigroup IsMain where
  NotMain <> _ = NotMain
  _       <> NotMain = NotMain
  IsMain  <> IsMain = IsMain

instance Monoid IsMain where
  mempty = IsMain
  mappend = (<>)

doCompile :: Monoid r => (IsMain -> Interface -> TCM r) -> IsMain -> Interface -> TCM r
doCompile f isMain i = do
  flip evalStateT Set.empty $ compilePrim $ doCompile' f isMain i
  where
  -- The Agda.Primitive module is only loaded if the --no-load-primitives flag was not given,
  -- thus, only try to compile it if we have visited it.
  compilePrim cont = do
    agdaPrim <- lift $ do
      agdaPrim <- TCM.topLevelModuleName agdaPrim
      Map.lookup agdaPrim <$> getVisitedModules
    case agdaPrim of
      Nothing   -> cont
      Just prim ->
        mappend <$> doCompile' f NotMain (miInterface prim) <*> cont
    where
    agdaPrim = RawTopLevelModuleName
      { rawModuleNameRange = mempty
      , rawModuleNameParts = "Agda" :| "Primitive" : []
      }
      -- N.B. The Range in TopLevelModuleName is ignored for Ord, so we can set it to mempty.

-- This helper function is called for both `Agda.Primitive` and the module in question.
-- It's also called for each imported module, recursively. (Avoiding duplicates).
doCompile'
  :: Monoid r
  => (IsMain -> Interface -> TCM r) -> (IsMain -> Interface -> StateT (Set ModuleName) TCM r)
doCompile' f isMain i = do
  alreadyDone <- gets (Set.member (iModuleName i))
  if alreadyDone then return mempty else do
    imps <- lift $
      map miInterface . catMaybes <$>
        mapM (getVisitedModule . fst) (iImportedModules i)
    ri <- mconcat <$> mapM (doCompile' f NotMain) imps
    lift $ setInterface i
    r <- lift $ f isMain i
    modify (Set.insert $ iModuleName i)
    return $ mappend ri r

setInterface :: Interface -> TCM ()
setInterface i = do
  opts <- getsTC (stPersistentOptions . stPersistentState)
  setCommandLineOptions opts
  mapM_ setOptionsFromPragma (iDefaultPragmaOptions i ++ iFilePragmaOptions i)
  -- One could perhaps make the following command lazy. Note, however,
  -- that it doesn't suffice to replace setTCLens' with setTCLens,
  -- because the stPreImportedModules field is strict.
  stImportedModules `setTCLens'`
    Set.fromList (map fst (iImportedModules i))
  stCurrentModule `setTCLens'`
    Just (iModuleName i, iTopLevelModuleName i)

curIF :: ReadTCState m => m Interface
curIF = do
  name <- curMName
  maybe __IMPOSSIBLE__ miInterface <$> getVisitedModule name

curMName :: ReadTCState m => m TopLevelModuleName
curMName = maybe __IMPOSSIBLE__ snd <$> useTC stCurrentModule

curDefs :: ReadTCState m => m Definitions
curDefs = HMap.filter (not . defNoCompilation) . (^. sigDefinitions) . iSignature <$> curIF

sortDefs :: Definitions -> [(QName, Definition)]
sortDefs defs =
  -- The list is sorted to ensure that the order of the generated
  -- definitions does not depend on things like the number of bits
  -- in an Int (see Issue 1900).
  sortBy (compare `on` fst) $
  HMap.toList defs

compileDir :: HasOptions m => m FilePath
compileDir = do
  mdir <- optCompileDir <$> commandLineOptions
  maybe __IMPOSSIBLE__ return mdir


repl :: [String] -> String -> String
repl subs = go where
  go ('<':'<':c:'>':'>':s) | 0 <= i && i < length subs = subs !! i ++ go s
     where i = ord c - ord '0'
  go (c:s) = c : go s
  go []    = []


-- | Sets up the compilation environment.
inCompilerEnv :: CheckResult -> TCM a -> TCM a
inCompilerEnv checkResult cont = do
  let mainI = crInterface checkResult
      checkedSource = crSource checkResult

  -- Preserve the state (the compiler modifies the state).
  -- Andreas, 2014-03-23 But we might want to collect Benchmark info,
  -- so use localTCState.
  -- FNF, 2017-02-22 we also want to keep the warnings we have encountered,
  -- so use localTCStateSaving and pick them out.
  (a , s) <- localTCStateSaving $ do

    -- Compute the output directory. Note: using commandLineOptions would make
    -- the current pragma options persistent when we setCommandLineOptions
    -- below.
    opts <- getsTC $ stPersistentOptions . stPersistentState
    let compileDir = case optCompileDir opts of
          Just dir -> dir
          Nothing  ->
            -- The default output directory is the project root.
            let tm = iTopLevelModuleName mainI
                f  = srcFilePath $ srcOrigin checkedSource
            in filePath $ projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

    -- Andreas, 2017-08-23, issue #2714 recover pragma option --no-main
    -- Unfortunately, a pragma option is stored in the interface file as
    -- just a list of strings, thus, the solution is a bit of hack:
    -- We match on whether @["--no-main"]@ is one of the stored options.
    let iFilePragmaStrings = map pragmaStrings . iFilePragmaOptions
    when (["--no-main"] `elem` iFilePragmaStrings mainI) $
      setTCLens (stPragmaOptions . lensOptCompileMain . lensCollapseDefault) False

    -- Perhaps all pragma options from the top-level module should be
    -- made available to the compiler in a suitable way. Here are more
    -- hacks:
    when (any ("--cubical" `elem`) $ iFilePragmaStrings mainI) $
      setTCLens (stPragmaOptions . lensOptCubical) $ Just CFull
    when (any ("--erased-cubical" `elem`) $ iFilePragmaStrings mainI) $
      setTCLens (stPragmaOptions . lensOptCubical) $ Just CErased

    setScope (iInsideScope mainI) -- so that compiler errors don't use overly qualified names
    ignoreAbstractMode cont
  -- keep generated warnings
  let newWarnings = stPostTCWarnings $  stPostScopeState $ s
  stTCWarnings `setTCLens` newWarnings
  return a

topLevelModuleName ::
  ReadTCState m => ModuleName -> m TopLevelModuleName
topLevelModuleName m = do
  -- Interfaces of visited modules.
  visited <- map miInterface . Map.elems <$> getVisitedModules
  -- find the module with the longest matching prefix to m
  let is = sortBy (compare `on` (length . mnameToList . iModuleName)) $
           filter (\i -> mnameToList (iModuleName i) `isPrefixOf`
                         mnameToList m)
             visited
  case is of
    (i : _) -> return (iTopLevelModuleName i)
    -- if we did not get anything, it may be because m is a section
    -- (a module _ ), see e.g. #1866
    []       -> curMName
