
-- | Generate an import dependency graph for a given module.

module Agda.Interaction.Highlighting.Dot where

import Control.Monad.State

import qualified Data.Map as M
import Data.Map(Map)
import Data.Maybe

import qualified Data.Set as S
import Data.Set (Set)

import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy as BS

import Agda.Syntax.Abstract
import Agda.TypeChecking.Monad

import Agda.Utils.Pretty

-- | Internal module identifiers for construction of dependency graph.
type ModuleId = L.Text

data DotState = DotState
  { dsModules    :: Map ModuleName ModuleId
    -- ^ Records already processed modules
    --   and maps them to an internal identifier.
  , dsNameSupply :: [ModuleId]
    -- ^ Supply of internal identifiers.
  , dsConnection :: Set (ModuleId, ModuleId)
    -- ^ Edges of dependency graph.
  }

initialDotState :: DotState
initialDotState = DotState
  { dsModules    = mempty
  , dsNameSupply = map (L.pack . ('m':) . show) [0..]
  , dsConnection = mempty
  }

type DotM = State DotState

-- | Translate a 'ModuleName' to an internal 'ModuleId'.
--   Returns @True@ if the 'ModuleName' is new, i.e., has not been
--   encountered before and is thus added to the map of processed modules.
addModule :: ModuleName -> DotM (ModuleId, Bool)
addModule m = do
    s <- get
    case M.lookup m (dsModules s) of
        Just r  -> return (r, False)
        Nothing -> do
            let newName:nameSupply = dsNameSupply s
            put s
              { dsModules = M.insert m newName (dsModules s)
              , dsNameSupply = nameSupply
              }
            return (newName, True)

-- | Add an arc from importer to imported.
addConnection :: ModuleId -> ModuleId -> DotM ()
addConnection m1 m2 = modify $ \s -> s {dsConnection = S.insert (m1,m2) (dsConnection s)}

-- | Recursively build import graph, starting from given 'Interface'.
--   Modifies the state in 'DotM' and returns the 'ModuleId' of the 'Interface'.
dottify :: VisitedModules -> Interface -> DotState
dottify visitedModules iface = execState (dottify' visitedModules iface) initialDotState

dottify' :: VisitedModules -> Interface -> DotM ModuleId
dottify' visitedModules iface = do
    let curModule = iModuleName iface
    (name, continue) <- addModule curModule
    -- If we have not visited this interface yet,
    -- process its imports recursively and
    -- add them as connections to the graph.
    when continue $ do
      let importedModuleNames = map (toTopLevelModuleName . fst) (iImportedModules iface)
      let importedModuleInfos = mapMaybe (flip M.lookup visitedModules) importedModuleNames
      let importedIfaces = map miInterface importedModuleInfos
      imports <- mapM (dottify' visitedModules) importedIfaces
      mapM_ (addConnection name) imports
    return name

renderDot :: DotState -> L.Text
renderDot st = L.unlines $ concat
  [ [ "digraph dependencies {" ]
  , [ L.concat ["   ", repr, "[label=\"", L.pack (prettyShow (mnameToConcrete modulename)), "\"];"]
    | (modulename, repr) <- M.toList (dsModules st) ]
  , [ L.concat ["   ", r1, " -> ", r2, ";"]
    | (r1 , r2) <- S.toList (dsConnection st) ]
  , ["}"]
  ]

renderDotToFile :: MonadIO m => DotState -> FilePath -> m ()
renderDotToFile dot fp = liftIO $ BS.writeFile fp $ E.encodeUtf8 $ renderDot dot

getDot :: Interface -> TCM DotState
getDot iface = do
  visitedModules <- getVisitedModules
  return (dottify visitedModules iface)

-- | Generate a .dot file for the import graph starting with the
--   given 'Interface' and write it to the file specified by the
--   command line option.
generateDot :: Interface -> FilePath -> TCM ()
generateDot iface fp = do
  dot <- getDot iface
  renderDotToFile dot fp
