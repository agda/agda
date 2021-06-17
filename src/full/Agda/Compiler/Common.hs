{-# LANGUAGE CPP #-}

module Agda.Compiler.Common where

import Data.List as List
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap
import Data.Char
import Data.Function
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Control.Monad
import Control.Monad.State

import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I

import Agda.Interaction.FindFile ( srcFilePath )
import Agda.Interaction.Options
import Agda.Interaction.Imports ( CheckResult, crInterface, crSource, Source(..) )

import Agda.TypeChecking.Monad

import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Pretty

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
  -- The Agda.Primitive module is implicitly assumed to be always imported,
  -- even though it not necesseraly occurs in iImportedModules.
  -- TODO: there should be a better way to get hold of Agda.Primitive?
  [agdaPrimInter] <- filter (("Agda.Primitive"==) . prettyShow . iModuleName)
    . map miInterface . Map.elems
      <$> getVisitedModules
  flip evalStateT Set.empty $ mappend <$> doCompile' f NotMain agdaPrimInter <*> doCompile' f isMain i

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
        mapM (getVisitedModule . toTopLevelModuleName . fst) (iImportedModules i)
    ri <- mconcat <$> mapM (doCompile' f NotMain) imps
    lift $ setInterface i
    r <- lift $ f isMain i
    modify (Set.insert $ iModuleName i)
    return $ mappend ri r

setInterface :: Interface -> TCM ()
setInterface i = do
  opts <- getsTC (stPersistentOptions . stPersistentState)
  setCommandLineOptions opts
  mapM_ setOptionsFromPragma (iPragmaOptions i)
  stImportedModules `setTCLens` Set.fromList (map fst $ iImportedModules i)
  stCurrentModule   `setTCLens` Just (iModuleName i)

curIF :: ReadTCState m => m Interface
curIF = do
  name <- curMName
  maybe __IMPOSSIBLE__ miInterface <$> getVisitedModule (toTopLevelModuleName name)

curMName :: ReadTCState m => m ModuleName
curMName = fromMaybe __IMPOSSIBLE__ <$> useTC stCurrentModule

curDefs :: ReadTCState m => m Definitions
curDefs = HMap.filter (not . defNoCompilation) . (^. sigDefinitions) . iSignature <$> curIF

sortDefs :: Definitions -> [(QName, Definition)]
sortDefs defs =
  -- The list is sorted to ensure that the order of the generated
  -- definitions does not depend on things like the number of bits
  -- in an Int (see Issue 1900).
  List.sortBy (compare `on` fst) $
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
            let tm = toTopLevelModuleName $ iModuleName mainI
                f  = srcFilePath $ srcOrigin checkedSource
            in filePath $ C.projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

    -- Andreas, 2017-08-23, issue #2714 recover pragma option --no-main
    -- Unfortunately, a pragma option is stored in the interface file as
    -- just a list of strings, thus, the solution is a bit of hack:
    -- We match on whether @["--no-main"]@ is one of the stored options.
    when (["--no-main"] `elem` iPragmaOptions mainI) $
      stPragmaOptions `modifyTCLens` \ o -> o { optCompileNoMain = True }

    setScope (iInsideScope mainI) -- so that compiler errors don't use overly qualified names
    ignoreAbstractMode cont
  -- keep generated warnings
  let newWarnings = stPostTCWarnings $  stPostScopeState $ s
  stTCWarnings `setTCLens` newWarnings
  return a

topLevelModuleName :: ReadTCState m => ModuleName -> m ModuleName
topLevelModuleName m = do
  -- get the names of the visited modules
  visited <- List.map (iModuleName . miInterface) . Map.elems <$>
    getVisitedModules
  -- find the module with the longest matching prefix to m
  let ms = sortBy (compare `on` (length . mnameToList)) $
       List.filter (\ m' -> mnameToList m' `isPrefixOf` mnameToList m) visited
  case ms of
    (m' : _) -> return m'
    -- if we did not get anything, it may be because m is a section
    -- (a module _ ), see e.g. #1866
    []       -> curMName
