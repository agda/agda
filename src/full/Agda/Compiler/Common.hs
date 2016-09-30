{-# LANGUAGE CPP #-}

module Agda.Compiler.Common where


#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (foldl, mapM_, mapM, sequence, concat)
#endif

import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char
import Data.Function

import Control.Monad
import Control.Monad.State  hiding (mapM_, forM_, mapM, forM, sequence)

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I

import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.FileName
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

data IsMain = IsMain | NotMain
  deriving (Eq, Show)

doCompile :: IsMain -> Interface -> (IsMain -> Interface -> TCM ()) -> TCM ()
doCompile isMain i f = do
  -- The Agda.Primitive module is implicitly assumed to be always imported,
  -- even though it not necesseraly occurs in iImportedModules.
  -- TODO: there should be a better way to get hold of Agda.Primitive?
  [agdaPrimInter] <- filter (("Agda.Primitive"==) . prettyShow . iModuleName)
    . map miInterface . Map.elems
      <$> getVisitedModules
  flip evalStateT Set.empty $ comp NotMain agdaPrimInter >> comp isMain i
  where
    comp :: IsMain -> Interface -> StateT (Set ModuleName) TCM ()
    comp isMain i = do
      alreadyDone <- Set.member (iModuleName i) <$> get
      when (not alreadyDone) $ do
        imps <- lift $
          map miInterface . catMaybes <$>
            mapM (getVisitedModule . toTopLevelModuleName . fst) (iImportedModules i)
        mapM_ (comp NotMain) imps
        lift $ setInterface i
        lift $ f isMain i
        modify (Set.insert $ iModuleName i)

setInterface :: Interface -> TCM ()
setInterface i = do
  opts <- gets (stPersistentOptions . stPersistentState)
  setCommandLineOptions opts
  mapM_ setOptionsFromPragma (iPragmaOptions i)
  stImportedModules .= Set.empty
  stCurrentModule   .= Just (iModuleName i)

curIF :: TCM Interface
curIF = do
  mName <- use stCurrentModule
  case mName of
    Nothing   -> __IMPOSSIBLE__
    Just name -> do
      mm <- getVisitedModule (toTopLevelModuleName name)
      case mm of
        Nothing -> __IMPOSSIBLE__
        Just mi -> return $ miInterface mi


curSig :: TCM Signature
curSig = iSignature <$> curIF

curMName :: TCM ModuleName
curMName = sigMName <$> curSig

curDefs :: TCM Definitions
curDefs = (^. sigDefinitions) <$> curSig

sortDefs :: Definitions -> [(QName, Definition)]
sortDefs defs =
  -- The list is sorted to ensure that the order of the generated
  -- definitions does not depend on things like the number of bits
  -- in an Int (see Issue 1900).
  List.sortBy (compare `on` fst) $
  HMap.toList defs

sigMName :: Signature -> ModuleName
sigMName sig = case Map.keys (sig ^. sigSections) of
  []    -> __IMPOSSIBLE__
  m : _ -> m


compileDir :: TCM FilePath
compileDir = do
  mdir <- optCompileDir <$> commandLineOptions
  case mdir of
    Just dir -> return dir
    Nothing  -> __IMPOSSIBLE__


repl :: [String] -> String -> String
repl subs = go where
  go ('<':'<':c:'>':'>':s) | 0 <= i && i < length subs = subs !! i ++ go s
     where i = ord c - ord '0'
  go (c:s) = c : go s
  go []    = []


-- | Copy pasted from MAlonzo....
--   Move somewhere else!
conArityAndPars :: QName -> TCM (Nat, Nat)
conArityAndPars q = do
  def <- getConstInfo q
  TelV tel _ <- telView $ defType def
  let Constructor{ conPars = np } = theDef def
      n = length (telToList tel)
  return (n - np, np)

-- | Sets up the compilation environment.
inCompilerEnv :: Interface -> TCM a -> TCM a
inCompilerEnv mainI cont =
  -- Preserve the state (the compiler modifies the state).
  -- Andreas, 2014-03-23 But we might want to collect Benchmark info,
  -- so use localTCState.
  localTCState $ do

    -- Compute the output directory. Note: using commandLineOptions would make
    -- the current pragma options persistent when we setCommandLineOptions
    -- below.
    opts <- gets $ stPersistentOptions . stPersistentState
    compileDir <- case optCompileDir opts of
      Just dir -> return dir
      Nothing  -> do
        -- The default output directory is the project root.
        let tm = toTopLevelModuleName $ iModuleName mainI
        f <- findFile tm
        return $ filePath $ C.projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

    ignoreAbstractMode $ do
      cont

topLevelModuleName :: ModuleName -> TCM ModuleName
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
