
-- | Generate an import dependency graph for a given module.

module Agda.Interaction.Highlighting.Dot where

import Control.Monad.State

import qualified Data.Map as M
import Data.Map(Map)
import Data.Maybe

import qualified Data.Set as S
import Data.Set (Set)

import Agda.Interaction.Options
import Agda.Syntax.Abstract
import Agda.TypeChecking.Monad

import Agda.Utils.Impossible

-- | Internal module identifiers for construction of dependency graph.
type ModuleId = String

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
  , dsNameSupply = map (('m':) . show) [0..]
  , dsConnection = mempty
  }

type DotM = StateT DotState TCM

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
dottify :: Interface -> DotM ModuleId
dottify inter = do
    let curModule = iModuleName inter
    (name, continue) <- addModule curModule
    -- If we have not visited this interface yet,
    -- process its imports recursively and
    -- add them as connections to the graph.
    when continue $ do
        importsifs <- lift $ map miInterface . catMaybes <$>
          mapM (getVisitedModule . toTopLevelModuleName . fst) (iImportedModules inter)
        imports    <- mapM dottify importsifs
        mapM_ (addConnection name) imports
    return name

-- | Generate a .dot file for the import graph starting with the
--   given 'Interface' and write it to the file specified by the
--   command line option.
generateDot :: Interface -> TCM ()
generateDot inter = do
    (top, state) <- flip runStateT initialDotState $ do
        dottify inter
    fp <- fromMaybe __IMPOSSIBLE__ . optDependencyGraph <$> commandLineOptions
    liftIO $ writeFile fp $ mkDot state
  where
    mkDot :: DotState -> String
    mkDot st = unlines $
        [ "digraph dependencies {"
        ] ++ ["   " ++ repr ++ "[label=\"" ++ show (mnameToConcrete modulename) ++ "\"];"
             | (modulename, repr) <- M.toList (dsModules st)]
          ++ ["   " ++ r1 ++ " -> " ++ r2 ++ ";"
             | (r1 , r2) <- S.toList (dsConnection st) ]
          ++ ["}"]
