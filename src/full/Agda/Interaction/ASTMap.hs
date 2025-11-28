module Agda.Interaction.ASTMap
  ( buildAstMapFromExprLike
  , WrapperMode(..)
  ) where

import Prelude
import Control.Monad.State.Strict (State, execState, get, put)
import Data.List  (sortBy)
import Data.Ord   (comparing)
import Data.Word  (Word32)
import qualified Data.IntMap.Strict as IM
import qualified Data.DList         as DL

import Agda.Syntax.Position
  ( HasRange(getRange), rangeToPosPair )
import Agda.Syntax.Abstract.Views
  ( ExprLike(..) )  -- needs foldExprLike + ctorName + isWrapper from your instance(s)

import Agda.Interaction.Response.Base
  ( AstPositions(..)
  , AstNodeId
  , AstNode(..)
  , AstMapPayload(..)
  )

--------------------------------------------------------------------------------
-- Public API

-- | How to treat \"wrapper\" nodes supplied by 'isWrapper'.
--   'OpaqueWrappers' means wrappers are not emitted as AST nodes (their single
--   child is effectively spliced in their place). 'IncludeWrappers' preserves
--   the original nodes exactly as produced by the 'ExprLike' fold.
data WrapperMode
  = IncludeWrappers
  | OpaqueWrappers
  deriving (Eq, Show)

-- | Build a whole-file *forest* AST map from any list of 'ExprLike' values.
--   - 'AstPositions' selects the coordinate system (recommended: 'AstCodepoint').
--   - UTF-8 is assumed globally (no encoding in the payload by design).
--   - 'WrapperMode' chooses whether 'isWrapper' nodes are included as nodes
--     ('IncludeWrappers') or treated as transparent ('OpaqueWrappers').
buildAstMapFromExprLike
  :: forall a. ExprLike a
  => WrapperMode    -- ^ wrapper handling
  -> AstPositions   -- ^ coordinate system
  -> [a]            -- ^ roots
  -> AstMapPayload
buildAstMapFromExprLike wmode posKind roots =
  let
    -- 1) Flatten all roots into ranged nodes (kind, beg, end)
    flat0 :: [FlatNode]
    flat0 = concatMap (collectFlat wmode) roots

    -- 2) Remove invalid/empty, sort by (beg ASC, end DESC) for containment scan
    flat :: [FlatNode]
    flat =
      sortBy (comparing fnBeg <> flip (comparing fnEnd))
      $ filter (\fn -> fnBeg fn < fnEnd fn) flat0

    -- 3) Build forest: ids, children, and top-level ids
    Build{ bNodes = nodesMap, bOrder = order, bTopLevel = tops } =
      buildByContainment flat

    -- 4) Materialize node list in creation order
    orderedNodes :: [AstNode]
    orderedNodes = map (\i -> nodesMap IM.! i2i i) order
  in
    AstMapPayload
      { astPositions   = posKind
      , astTopLevel    = tops
      , astNodes       = orderedNodes
      }

--------------------------------------------------------------------------------
-- Internals

-- A single flat (pre-tree) node harvested from an 'ExprLike' fold
data FlatNode = FlatNode
  { fnKind :: !String
  , fnBeg  :: !Word32
  , fnEnd  :: !Word32
  } deriving (Eq, Show)

-- Collect a flat list of nodes from one 'ExprLike' root, optionally omitting
-- wrapper nodes while still traversing into their (single) child.
collectFlat :: forall a. ExprLike a => WrapperMode -> a -> [FlatNode]
collectFlat wmode x =
  DL.toList $ foldExprLike go x
  where
    go :: forall b. ExprLike b => b -> DL.DList FlatNode
    go node =
      case rangeToPosPair (getRange node) of
        Just (s, e) | s < e ->
          let beg = fromIntegral s :: Word32
              end = fromIntegral e :: Word32
              kd  = ctorName node
              emit = DL.singleton (FlatNode kd beg end)
          in  case wmode of
                -- Keep wrappers as ordinary nodes.
                IncludeWrappers -> emit
                -- Hide wrappers: do not emit the wrapper itself,
                -- but still traverse (foldExprLike already visits children).
                OpaqueWrappers  -> if isWrapper node then mempty else emit
        _ -> mempty

-- Builder state for deriving a forest by containment
data Build = Build
  { bNextId   :: !AstNodeId                       -- next fresh id (starts at 1)
  , bStack    :: [(AstNodeId, Word32)]            -- open containers: (id, end)
  , bNodes    :: IM.IntMap AstNode                -- id → node (without children until closed)
  , bKids     :: IM.IntMap (DL.DList AstNodeId)   -- id → accumulated children
  , bOrder    :: [AstNodeId]                      -- creation order (deterministic output)
  , bTopLevel :: [AstNodeId]                      -- nodes with no parent (forest roots)
  } deriving (Show)

emptyBuild :: Build
emptyBuild = Build
  { bNextId   = 1
  , bStack    = []
  , bNodes    = IM.empty
  , bKids     = IM.empty
  , bOrder    = []
  , bTopLevel = []
  }

-- Turn a sorted flat list into a forest using a containment stack
buildByContainment :: [FlatNode] -> Build
buildByContainment xs = execState (mapM_ step xs) emptyBuild
  where
    step :: FlatNode -> State Build ()
    step FlatNode{..} = do
      -- Close all finished containers before placing this node
      popFinished fnBeg
      -- Allocate & insert node
      bid <- freshId
      insertNode bid fnKind fnBeg fnEnd
      -- Attach to the current parent if any; otherwise it’s a top-level root
      attachToParent bid
      -- Become the new innermost container
      pushContainer bid fnEnd

    freshId :: State Build AstNodeId
    freshId = do
      st <- get
      let i = bNextId st
      put st{ bNextId = i + 1 }
      pure i

    insertNode :: AstNodeId -> String -> Word32 -> Word32 -> State Build ()
    insertNode i kd b e = do
      st <- get
      let node = AstNode
            { astNodeId       = i
            , astNodeKind     = kd
            , astNodeBeg      = b
            , astNodeEnd      = e
            , astNodeChildren = [] }
      put st
        { bNodes = IM.insert (i2i i) node (bNodes st)
        , bKids  = IM.insert (i2i i) mempty (bKids st)
        , bOrder = bOrder st ++ [i]
        }

    attachToParent :: AstNodeId -> State Build ()
    attachToParent i = do
      st <- get
      case bStack st of
        [] -> put st{ bTopLevel = bTopLevel st ++ [i] }
        (p, _):_ ->
          put st{ bKids = IM.adjust (<> DL.singleton i) (i2i p) (bKids st) }

    pushContainer :: AstNodeId -> Word32 -> State Build ()
    pushContainer i e = do
      st <- get
      put st{ bStack = (i, e) : bStack st }

    popFinished :: Word32 -> State Build ()
    popFinished curBeg = do
      st <- get
      case bStack st of
        [] -> pure ()
        (j, endJ):rest
          | endJ <= curBeg -> do
              -- finalize j with its accumulated children
              let kids = maybe [] DL.toList (IM.lookup (i2i j) (bKids st))
                  node = (bNodes st IM.! i2i j){ astNodeChildren = kids }
              put st{ bStack = rest
                    , bNodes = IM.insert (i2i j) node (bNodes st) }
              popFinished curBeg
          | otherwise -> pure ()

-- small helper
i2i :: AstNodeId -> Int
i2i = fromIntegral
