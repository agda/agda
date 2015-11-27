{-# LANGUAGE CPP #-}

module Agda.Compiler.Common where


#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (foldl, mapM_, mapM, sequence, concat)
#endif

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char

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
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

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
