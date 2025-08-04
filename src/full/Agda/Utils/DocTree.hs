{-# LANGUAGE CPP #-}

-- | A simple document tree to render @'Doc' ann@ but preserve annotations.
--
-- 'DocTree' and 'renderToTree'' originally taken from
-- <https://github.com/plt-amy/agda/blob/9fd50b883f14a05792ed79a0b693fbecb2165bf5/src/full/Agda/LSP/Output.hs>
-- but rewritten to encode more invariants.

module Agda.Utils.DocTree
  ( DocTree( Node, Text )
  , prettyDocTree
  , renderToTree
  , renderToTree'
  , renderTree'
  , treeToText
  , treeToTextNoAnn
  )
where

import Prelude hiding (null)

import Control.DeepSeq (NFData(..))
import Data.Text          (Text)
import Data.Text          qualified as Text
#if MIN_VERSION_text(2,0,2)
import Data.Text.Encoding (strictBuilderToText, textToStrictBuilder)
#else
-- GHC 9.2 ships text-1.2.5.0
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder qualified as Builder
#endif

import GHC.Generics

import Text.PrettyPrint.Annotated.HughesPJ (Doc)
import Text.PrettyPrint.Annotated.HughesPJ qualified as Ppr

import Agda.Utils.List1 (List1, pattern (:|), (<|))
import Agda.Utils.List1 qualified as List1
import Agda.Utils.Null

import Agda.Utils.Impossible
import Agda.Utils.Function (applyUnless)

-- | A rendered document with annotations from type @ann@.
data DocTree ann
  = Node ann [DocTree ann]
     -- ^ Stuff annotated by @ann@.
  | Text Text
     -- ^ Atom.
  deriving (Generic, Show)

instance Null (DocTree ann) where
  empty = Text mempty
  null = \case
    Node a ts -> all null ts
    Text t    -> null t

instance NFData ann => NFData (DocTree ann) where

---------------------------------------------------------------------------
-- * Converting 'DocTree' to 'Doc'

prettyDocTree :: DocTree ann -> Doc ann
prettyDocTree = \case
  Text t    -> Ppr.text $ Text.unpack t  -- Bad, we should have a Doc that supports Text
  Node a ts -> Ppr.annotate a $ foldMap prettyDocTree ts

---------------------------------------------------------------------------
-- * Converting 'Doc' to 'DocTree'
--
-- Implemented as state machine where the state is a stack of unclosed
-- annotation with the annotated stuff inbetween.

-- | State of the right-to-left conversion to tree.
data St ann = St
  { front :: String
      -- ^ Accumulator for text.
  , stack :: List1 (Item ann)
      -- ^ A nonempty stack of annotated trees with their closing annotation bracket,
      --   waiting for the opening bracket.
  }

-- | Annotated stuff waiting for the opening bracket.
data Item ann = Item ann [DocTree ann]

-- Initial state.
instance Null ann => Null (St ann) where
  empty = St empty (List1.singleton empty)
  null (St s is) = null s && all null is

instance Null ann => Null (Item ann) where
  empty = Item empty empty
  null (Item a ts) = null a && null ts

type Width = Int
type Fill  = Float

-- | Render a @'Doc' ann@ to a @'DocTree' ann@ with the given layout parameters.
-- E.g. @width=100@ @fill=1.5@.
--
renderToTree' :: forall ann. Null ann => Width -> Fill -> Doc ann -> DocTree ann
renderToTree' width fill =
    finalize . Ppr.fullRenderAnn Ppr.PageMode width fill go empty
  where
    -- State machine transition for the right-to-left automaton.
    go :: Ppr.AnnotDetails ann -> St ann -> St ann
    go = \case
      Ppr.AnnotStart  -> annotStart
      Ppr.NoAnnot d _ -> noAnnot d
      Ppr.AnnotEnd a  -> annotEnd a

    finalize :: St ann -> DocTree ann
    finalize (St s (Item a ts :| is))
      | null is   = mkNode a s ts
      | otherwise = __IMPOSSIBLE__  -- not well-bracketed

    -- Create a node once the opening bracket has been reached.
    mkNode :: ann -> String -> [DocTree ann] -> DocTree ann
    mkNode a s ts = Node a $ applyUnless (null s) (Text (Text.pack s) :) ts

    -- Got the opening bracket on an annotation:
    -- Pop an item from the stack
    annotStart :: St ann -> St ann
    annotStart (St s (Item a ts :| is1)) =
      case is1 of
        i : is -> St "" (consTree (mkNode a s ts) i :| is)
        []     -> __IMPOSSIBLE__  -- not well-bracketed
      where
        consTree :: DocTree ann -> Item ann -> Item ann
        consTree t (Item a ts) = Item a (t : ts)

    -- Got text.
    noAnnot :: Ppr.TextDetails -> St ann -> St ann
    noAnnot (Ppr.Chr  c) (St s0 is) = St (c : s0) is
    noAnnot (Ppr.Str  s) (St s0 is) = St (s ++ s0) is
    noAnnot (Ppr.PStr s) (St s0 is) = St (s ++ s0) is

    -- Got the closing bracket of a new annotation:
    -- Push a new item on the stack.
    annotEnd :: ann -> St ann -> St ann
    annotEnd a (St s is1) = St "" (Item a [] <| pushStr s is1)
      where
        pushStr :: String -> List1 (Item ann) -> List1 (Item ann)
        pushStr "" is1 = is1
        pushStr s (Item a ts :| is) = Item a (Text (Text.pack s) : ts) :| is

-- | Render a @'Doc' ann@ to a @'DocTree' ann@ using standard layout parameters.
renderToTree :: forall ann. Null ann => Doc ann -> DocTree ann
renderToTree = renderToTree' 100 1.5

---------------------------------------------------------------------------
-- * Converting 'DocTree' to 'Text' et al.

-- | Generic 'DocTree' linearization.
renderTree' :: forall ann t. Monoid t => (Text -> t) -> (ann -> t -> t) -> DocTree ann -> t
renderTree' txt ann = go
  where
    go :: DocTree ann -> t
    go = \case
      Node a ts -> ann a $ foldMap go ts
      Text t    -> txt t

-- | Linearize a 'DocTree' to 'Text' with the given 'Text'-rendering of the annotations.
treeToText :: (ann -> Text -> Text) -> DocTree ann -> Text
treeToText ann =
#if MIN_VERSION_text(2,0,2)
  strictBuilderToText . renderTree' textToStrictBuilder \ a -> textToStrictBuilder . ann a . strictBuilderToText
#else
  toText . renderTree' Builder.fromText \ a -> Builder.fromText . ann a . toText
  where
    toText = TL.toStrict . Builder.toLazyText
#endif
-- Naive implementation:
-- treeToText = renderTree' id

-- | Linearize a 'DocTree' to 'Text' dropping all annotations.
treeToTextNoAnn :: DocTree ann -> Text
treeToTextNoAnn = treeToText (const id)
