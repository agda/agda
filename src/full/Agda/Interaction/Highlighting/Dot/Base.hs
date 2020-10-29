{-# LANGUAGE GADTs #-}
-- | Generate an import dependency graph for a given module.

module Agda.Interaction.Highlighting.Dot.Base
  ( dottify
  , renderDotToFile
  , renderDot
  , DotGraph (..)
  , Env(..)
  ) where

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as M
import Data.Map(Map)

import qualified Data.Set as S
import Data.Set (Set)

import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy as BS

-- | Internal module identifiers for construction of dependency graph.
type NodeId = L.Text

-- | Graph structure
data DotGraph = DotGraph
  { dgNodeLabels :: Map NodeId L.Text
  , dgEdges      :: Set (NodeId, NodeId)
  }

-- * Graph construction monad

-- Read-only environment when constructing the graph.
data Env n where
  Env :: Ord n =>
    { deConnections :: n -> [n]
    -- ^ Names connected to an entity
    , deLabel       :: n -> L.Text
    -- ^ Rendering that entity's name to a label
    } -> Env n

data DotState n = DotState
  { dsNodeIds      :: Map n NodeId
    -- ^ Records already processed entities
    --   and maps them to an internal identifier.
  , dsNodeIdSupply :: [NodeId]
    -- ^ Supply of internal identifiers.
  , dsGraph        :: DotGraph
  }

initialDotState :: DotState n
initialDotState = DotState
  { dsNodeIds      = M.empty
  , dsNodeIdSupply = map (L.pack . ('m':) . show) [0..]
  , dsGraph        = DotGraph mempty mempty
  }

type DotM n a = Ord n => ReaderT (Env n) (State (DotState n)) a

runDotM :: Env n -> DotM n x -> DotGraph
runDotM env@Env{} = dsGraph . flip execState initialDotState . flip runReaderT env

getLabel :: n -> DotM n L.Text
getLabel = liftM2 deLabel ask . pure

getConnections :: n -> DotM n [n]
getConnections = liftM2 deConnections ask . pure

-- | Translate an entity name into an internal 'NodeId'.
--   Returns @True@ if the 'ModuleName' is new, i.e., has not been
--   encountered before and is thus added to the map of processed modules.
addEntity :: n -> DotM n (NodeId, Bool)
addEntity name = do
    s@(DotState nodeIds nodeIdSupply graph) <- get
    case M.lookup name nodeIds of
        Just nodeId  -> return (nodeId, False)
        Nothing -> do
            let newNodeId:remainingNodeIdSupply = nodeIdSupply
            label <- getLabel name
            put s
              { dsNodeIds      = M.insert name newNodeId nodeIds
              , dsNodeIdSupply = remainingNodeIdSupply
              , dsGraph        = graph
                { dgNodeLabels = M.insert newNodeId label . dgNodeLabels $ graph
                }
              }
            return (newNodeId, True)

-- | Add an arc from importer to imported.
addConnection :: NodeId -> NodeId -> DotM n ()
addConnection m1 m2 = modify $ \s -> s
  { dsGraph = (dsGraph s)
    { dgEdges = S.insert (m1, m2) . dgEdges . dsGraph $ s
    }
  }

dottify :: Env n -> n -> DotGraph
dottify env root = runDotM env (dottify' root)

dottify' :: n -> DotM n NodeId
dottify' entity = do
  (nodeId, continue) <- addEntity entity
  -- If we have not visited this interface yet,
  -- process its imports recursively and
  -- add them as connections to the graph.
  when continue $ do
    connectedEntities <- getConnections entity
    connectedNodeIds <- mapM dottify' connectedEntities
    mapM_ (addConnection nodeId) connectedNodeIds
  return nodeId

-- * Graph rendering

renderDot :: DotGraph -> L.Text
renderDot g = L.unlines $ concat
  [ [ "digraph dependencies {" ]
  , [ L.concat ["   ", nodeId, "[label=\"", label, "\"];"]
    | (nodeId, label) <- M.toList (dgNodeLabels g) ]
  , [ L.concat ["   ", r1, " -> ", r2, ";"]
    | (r1 , r2) <- S.toList (dgEdges g) ]
  , ["}"]
  ]

renderDotToFile :: MonadIO m => DotGraph -> FilePath -> m ()
renderDotToFile dot fp = liftIO $ BS.writeFile fp $ E.encodeUtf8 $ renderDot dot
