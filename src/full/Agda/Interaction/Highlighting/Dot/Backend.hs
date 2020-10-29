
module Agda.Interaction.Highlighting.Dot.Backend
  ( generateDot
  ) where

import Agda.Interaction.Highlighting.Dot.Base
  ( dottify
  , renderDotToFile
  , Env(Env, deConnections, deLabel)
  , DotGraph
  )

import qualified Data.Map as M
import qualified Data.Text.Lazy as L

import Agda.Syntax.Abstract
  ( ModuleName
  , mnameToConcrete
  , toTopLevelModuleName
  )

import Agda.TypeChecking.Monad
  ( Interface(iImportedModules, iModuleName)
  , getVisitedModules
  , miInterface
  , TCM
  , VisitedModules
  )

import Agda.Utils.Functor

import Agda.Utils.Pretty ( prettyShow )

-- * Module import graph generation

-- | Recursively build import graph, starting from given 'Interface'.
--   Modifies the state in 'DotM' and returns the 'NodeId' of the 'Interface'.

dottifyModuleImports :: VisitedModules -> ModuleName -> DotGraph
dottifyModuleImports visitedModules = dottify Env
  { deConnections = maybe [] getConnectedNames . getInterfaceByName
  , deLabel       = L.pack . prettyShow . mnameToConcrete
  }
  where
  getInterfaceByName = miInterface <.> (flip M.lookup visitedModules . toTopLevelModuleName)
  getConnectedNames = fst <.> iImportedModules

getDot :: Interface -> TCM DotGraph
getDot iface = do
  visitedModules <- getVisitedModules
  return (dottifyModuleImports visitedModules (iModuleName iface))

-- | Generate a .dot file for the import graph starting with the
--   given 'Interface' and write it to the file specified by the
--   command line option.
generateDot :: Interface -> FilePath -> TCM ()
generateDot iface fp = do
  dot <- getDot iface
  renderDotToFile dot fp
