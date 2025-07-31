-- | A simple document tree to render @'Doc' ann@ but preserve annotations.
--
-- 'DocTree' and 'renderToTree'' adapted from
-- <https://github.com/plt-amy/agda/blob/9fd50b883f14a05792ed79a0b693fbecb2165bf5/src/full/Agda/LSP/Output.hs>.

module Agda.Utils.DocTree where

import Prelude hiding (null)

import Data.Text          (Text)
import Data.Text          qualified as Text
import Data.Text.Encoding (StrictTextBuilder, strictBuilderToText, textToStrictBuilder)
import Data.Text.Encoding qualified as Text

import GHC.Generics

import Text.PrettyPrint.Annotated.HughesPJ (Doc)
import Text.PrettyPrint.Annotated.HughesPJ qualified as Ppr

import Agda.Utils.List (breakJust)
import Agda.Utils.Null

import Agda.Utils.Impossible

-- | A rendered document with annotations from type @ann@.
data DocTree ann
  = Node ann [DocTree ann]
  | Text Text
  | Mark ann
     -- ^ Delimits annotation, corresponds to 'Ppr.AnnotEnd'.
     --   Transient, does not occur in final 'DocTree'.
  deriving Generic

instance Null (DocTree ann) where
  empty = Text mempty
  null = \case
    Node _ ts -> all null ts
    Text t    -> Text.null t
    Mark _    -> False

type Width = Int
type Fill  = Float

-- | Linearize a 'DocTree' to 'Text' dropping all annotations.
treeToTextNoAnn :: DocTree ann -> Text
treeToTextNoAnn = treeToText (const id)

-- | Linearize a 'DocTree' to 'Text' with the given 'Text'-rendering of the annotations.
treeToText :: (ann -> Text -> Text) -> DocTree ann -> Text
treeToText ann = strictBuilderToText . renderTree' textToStrictBuilder \ a -> textToStrictBuilder . ann a . strictBuilderToText

-- | Generic 'DocTree' linearization.
renderTree' :: forall ann t. Monoid t => (Text -> t) -> (ann -> t -> t) -> DocTree ann -> t
renderTree' txt ann = go
  where
    go :: DocTree ann -> t
    go = \case
      Node a ts -> ann a $ foldMap go ts
      Text t    -> txt t
      Mark a    -> __IMPOSSIBLE__

-- | Render a @'Doc' ann@ to a @'DocTree' ann@ using standard layout parameters.
renderToTree :: forall ann. Null ann => Doc ann -> DocTree ann
renderToTree = renderToTree' 100 1.5

-- | Render a @'Doc' ann@ to a @'DocTree' ann@ with the given layout parameters.
-- E.g. @width=100@ @fill=1.5@.
renderToTree' :: forall ann. Null ann => Width -> Fill -> Doc ann -> DocTree ann
renderToTree' width fill =
    Node empty . Ppr.fullRenderAnn Ppr.PageMode width fill cont []
  where
    cont :: Ppr.AnnotDetails ann -> [DocTree ann] -> [DocTree ann]
    cont = \case
      Ppr.AnnotStart  -> annotate
      Ppr.NoAnnot d _ -> consText d
      Ppr.AnnotEnd a  -> (Mark a :)

    -- Find the closing bracket 'Mark' for the annotation
    annotate :: [DocTree ann] -> [DocTree ann]
    annotate ts =
      case breakJust isMark ts of
        (ts1, a, ts2)
          | null a    -> ts1 ++ ts2
          | otherwise -> Node a ts1 : ts2

    consText :: Ppr.TextDetails -> [DocTree ann] -> [DocTree ann]
    consText (Ppr.Chr  c) (Text t : ts) = Text (c `Text.cons` t) : ts
    consText (Ppr.Str  s) (Text t : ts) = Text (Text.pack s <> t) : ts
    consText (Ppr.PStr s) (Text t : ts) = Text (Text.pack s <> t) : ts
    consText (Ppr.Chr  c) ts            = Text (Text.singleton c) : ts
    consText (Ppr.Str  s) ts            = Text (Text.pack s) : ts
    consText (Ppr.PStr s) ts            = Text (Text.pack s) : ts

-- * Auxiliary functions

isMark :: DocTree ann -> Maybe ann
isMark = \case
  Mark a -> Just a
  Node{} -> Nothing
  Text{} -> Nothing
