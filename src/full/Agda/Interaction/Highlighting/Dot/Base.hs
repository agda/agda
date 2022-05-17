{-# LANGUAGE GADTs #-}
-- | Generate an import dependency graph for a given module.

module Agda.Interaction.Highlighting.Dot.Base
  ( renderDotToFile
  , renderDot
  , DotGraph
  ) where

import Control.Monad.IO.Class

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy as BS

import Agda.Utils.Graph.AdjacencyMap.Unidirectional
  (Graph, WithUniqueInt)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph

-- | Graph structure
type DotGraph = Graph (WithUniqueInt L.Text) ()

-- * Graph rendering

renderDot :: DotGraph -> L.Text
renderDot g = L.unlines $ concat
  [ [ "digraph dependencies {" ]
  , [ L.concat ["   ", show' nodeId, "[label=\"", label, "\"];"]
    | Graph.WithUniqueInt nodeId label <- S.toList $ Graph.nodes g
    ]
  , [ L.concat ["   ", show' r1, " -> ", show' r2, ";"]
    | Graph.Edge
        { source = Graph.WithUniqueInt r1 _
        , target = Graph.WithUniqueInt r2 _
        } <- Graph.edges g
    ]
  , ["}"]
  ]
  where
  show' = L.pack . ("m" ++) . show

renderDotToFile :: MonadIO m => DotGraph -> FilePath -> m ()
renderDotToFile dot fp = liftIO $ BS.writeFile fp $ E.encodeUtf8 $ renderDot dot
