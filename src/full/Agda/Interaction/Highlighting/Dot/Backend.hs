{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.Highlighting.Dot.Backend
  ( dotBackend
  ) where

import Agda.Interaction.Highlighting.Dot.Base (renderDotToFile)

import Control.Monad.Except
  ( ExceptT
  , runExceptT
  , MonadError(throwError)
  )
import Control.Monad.IO.Class
  ( MonadIO(..)
  )
import Control.DeepSeq

import Data.HashSet (HashSet)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import qualified Data.Text.Lazy as L

import GHC.Generics (Generic)

import Agda.Compiler.Backend (Backend(..), Backend'(..), Definition, Recompile(..))
import Agda.Compiler.Common (curIF, IsMain)

import Agda.Interaction.FindFile (findFile, srcFilePath)
import Agda.Interaction.Library
import Agda.Interaction.Options
  ( ArgDescr(ReqArg)
  , Flag
  , OptDescr(..)
  )

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import Agda.TypeChecking.Monad
  ( Interface(iImportedModules)
  , MonadTCError
  , ReadTCState
  , MonadTCM(..)
  , genericError
  , reportSDoc
  , getAgdaLibFiles
  )
import Agda.TypeChecking.Pretty

import Agda.Utils.Graph.AdjacencyMap.Unidirectional
  (Graph, WithUniqueInt)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Syntax.Common.Pretty ( prettyShow )

-- ------------------------------------------------------------------------

data DotFlags = DotFlags
  { dotFlagDestination :: Maybe FilePath
  , dotFlagLibraries   :: Maybe (HashSet String)
    -- ^ Only include modules from the given libraries.
  } deriving (Eq, Generic)

instance NFData DotFlags

defaultDotFlags :: DotFlags
defaultDotFlags = DotFlags
  { dotFlagDestination = Nothing
  , dotFlagLibraries   = Nothing
  }

dotFlagsDescriptions :: [OptDescr (Flag DotFlags)]
dotFlagsDescriptions =
  [ Option [] ["dependency-graph"] (ReqArg dependencyGraphFlag "FILE")
              "generate a Dot file with a module dependency graph"
  , Option [] ["dependency-graph-include"]
      (ReqArg includeFlag "LIBRARY")
      "include modules from the given library (default: all modules)"
  ]

dependencyGraphFlag :: FilePath -> Flag DotFlags
dependencyGraphFlag f o = return $ o { dotFlagDestination = Just f }

includeFlag :: String -> Flag DotFlags
includeFlag l o = return $
  o { dotFlagLibraries =
        case dotFlagLibraries o of
          Nothing -> Just (HashSet.singleton l)
          Just s  -> Just (HashSet.insert l s)
    }

data DotCompileEnv = DotCompileEnv
  { dotCompileEnvDestination :: FilePath
  , dotCompileEnvLibraries   :: Maybe (HashSet String)
    -- ^ Only include modules from the given libraries.
  }

-- Currently unused
data DotModuleEnv = DotModuleEnv

data DotModule = DotModule
  { dotModuleName          :: TopLevelModuleName
  , dotModuleImportedNames :: Set TopLevelModuleName
  , dotModuleInclude       :: Bool
    -- ^ Include the module in the graph?
  }

-- | Currently unused
data DotDef = DotDef

dotBackend :: Backend
dotBackend = Backend dotBackend'

dotBackend' :: Backend' DotFlags DotCompileEnv DotModuleEnv DotModule DotDef
dotBackend' = Backend'
  { backendName           = "Dot"
  , backendVersion        = Nothing
  , options               = defaultDotFlags
  , commandLineFlags      = dotFlagsDescriptions
  , isEnabled             = isJust . dotFlagDestination
  , preCompile            = asTCErrors . preCompileDot
  , preModule             = preModuleDot
  , compileDef            = compileDefDot
  , postModule            = postModuleDot
  , postCompile           = postCompileDot
  , scopeCheckingSuffices = True
  , mayEraseType          = const $ return True
  }

-- | Convert a general "MonadError String m" into "MonadTCError m".
asTCErrors :: MonadTCError m => ExceptT String m b -> m b
asTCErrors t = either genericError return =<< runExceptT t

preCompileDot
  :: MonadError String m
  => DotFlags
  -> m DotCompileEnv
preCompileDot d = case dotFlagDestination d of
  Just dest -> return $ DotCompileEnv
    { dotCompileEnvDestination = dest
    , dotCompileEnvLibraries   = dotFlagLibraries d
    }
  Nothing ->
    throwError "The Dot backend was invoked without being enabled!"

preModuleDot
  :: Applicative m
  => DotCompileEnv
  -> IsMain
  -> TopLevelModuleName
  -> Maybe FilePath
  -> m (Recompile DotModuleEnv DotModule)
preModuleDot _cenv _main _moduleName _ifacePath = pure $ Recompile DotModuleEnv

compileDefDot
  :: Applicative m
  => DotCompileEnv
  -> DotModuleEnv
  -> IsMain
  -> Definition
  -> m DotDef
compileDefDot _cenv _menv _main _def = pure DotDef

postModuleDot
  :: (MonadTCM m, ReadTCState m)
  => DotCompileEnv
  -> DotModuleEnv
  -> IsMain
  -> TopLevelModuleName
  -> [DotDef]
  -> m DotModule
postModuleDot cenv DotModuleEnv _main m _defs = do
  i <- curIF
  let importedModuleNames = Set.fromList $ fst <$> (iImportedModules i)
  include <- case dotCompileEnvLibraries cenv of
    Nothing -> return True
    Just ls -> liftTCM $ do
      f    <- findFile m
      libs <- getAgdaLibFiles (srcFilePath f) m

      let incLibs = filter (\l -> _libName l `HashSet.member` ls) libs
          inLib   = not (null incLibs)

      reportSDoc "dot.include" 10 $ do
        let name = pretty m
            list = nest 2 . vcat . map (text . _libName)
        if inLib then
          fsep
            ([ "Including"
             , name
             ] ++
             pwords "because it is in the following libraries:") $$
          list incLibs
        else
          fsep
            (pwords "Not including" ++
             [name <> ","] ++
             pwords "which is in the following libraries:") $$
          list libs

      return inLib

  return $ DotModule
    { dotModuleName          = m
    , dotModuleImportedNames = importedModuleNames
    , dotModuleInclude       = include
    }

postCompileDot
  :: (MonadIO m, ReadTCState m)
  => DotCompileEnv
  -> IsMain
  -> Map TopLevelModuleName DotModule
  -> m ()
postCompileDot cenv _main modulesByName =
  renderDotToFile moduleGraph (dotCompileEnvDestination cenv)
  where
  -- Only the keys of this map are used.
  modulesToInclude =
    Map.filter dotModuleInclude modulesByName

  moduleGraph :: Graph (WithUniqueInt L.Text) ()
  moduleGraph =
    Graph.renameNodesMonotonic (fmap (L.pack . prettyShow)) $
    Graph.transitiveReduction $
    Graph.filterNodesKeepingEdges
      (\n -> Graph.otherValue n `Map.member` modulesToInclude) $
    -- The following use of transitive reduction should not affect the
    -- semantics. It tends to make the graph smaller, so it might
    -- improve the overall performance of the code, but I did not
    -- verify this.
    Graph.transitiveReduction $
    Graph.addUniqueInts $
    Graph.fromEdges $
    concatMap
       (\ (name, m) ->
          [ Graph.Edge
              { source = name
              , target = target
              , label  = ()
              }
          | target <- Set.toList $ dotModuleImportedNames m
          ]) $
    Map.toList modulesByName
