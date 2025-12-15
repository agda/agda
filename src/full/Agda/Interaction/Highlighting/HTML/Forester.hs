module Agda.Interaction.Highlighting.HTML.Forester
  ( renderForesterHtml,
  )
where

import Data.ByteString (ByteString)
import Data.ByteString qualified as S (isInfixOf)
import Data.List (isInfixOf)
import Data.Monoid (mappend, mempty)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8)
import Data.Text.Lazy qualified as L
import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as B
import Text.Blaze.Html5
  ( Attribute,
    Html,
    Markup,
  )
import Text.Blaze.Internal
  ( ChoiceString (..),
    MarkupM (..),
    StaticString (getText),
  )

fromChoiceString ::
  -- | Decoder for bytestrings
  (ByteString -> Text) ->
  -- | String to render
  ChoiceString ->
  -- | Resulting builder
  Builder
fromChoiceString _ (Static s) = B.fromText $ getText s
fromChoiceString _ (String s) = B.fromText $ T.pack s
fromChoiceString _ (Text s) = B.fromText s
fromChoiceString d (ByteString s) = B.fromText $ d s
fromChoiceString d (PreEscaped x) = case x of
  String s -> B.fromText $ T.pack s
  Text s -> B.fromText s
  s -> fromChoiceString d s
fromChoiceString d (External x) = case x of
  -- Check that the sequence "</" is *not* in the external data.
  String s -> if "</" `isInfixOf` s then mempty else B.fromText (T.pack s)
  Text s -> if "</" `T.isInfixOf` s then mempty else B.fromText s
  ByteString s -> if "</" `S.isInfixOf` s then mempty else B.fromText (d s)
  s -> fromChoiceString d s
fromChoiceString d (AppendChoiceString x y) =
  fromChoiceString d x `mappend` fromChoiceString d y
fromChoiceString _ EmptyChoiceString = mempty
{-# INLINE fromChoiceString #-}

modify_open :: StaticString -> Text
modify_open open =
  let a = getText open
   in T.cons '<' (T.append "html:" (T.tail a))

modify_key :: StaticString -> Text
modify_key key =
  let a = getText key
   in T.dropEnd 2 (T.strip a)

-- Escape for forester lexer
wrap_verb :: Builder -> Builder
wrap_verb w = B.fromLazyText $ L.foldr go "" (B.toLazyText w)
  where
    go :: Char -> L.Text -> L.Text
    go '[' acc = L.append "\\startverb[\\stopverb" acc
    go ']' acc = L.append "\\startverb]\\stopverb" acc
    go x acc = L.cons x acc

renderMarkupBuilderWith ::
  (ByteString -> Text) ->
  Html ->
  Builder
renderMarkupBuilderWith d = go mempty
  where
    go :: Builder -> MarkupM b -> Builder
    go attrs (Parent _ open close content) =
      B.fromText "\\"
        `mappend` B.fromText (modify_open open)
        `mappend` B.fromText ">"
        `mappend` attrs
        `mappend` B.fromText "{"
        `mappend` go mempty content
        `mappend` B.fromText "}"
    go attrs (CustomParent tag content) =
      B.fromText "\\<html:"
        `mappend` fromChoiceString d tag
        `mappend` B.fromText ">"
        `mappend` attrs
        `mappend` B.fromText "{"
        `mappend` go mempty content
        `mappend` fromChoiceString d tag
        `mappend` B.fromText "}"
    go attrs (Leaf _ begin end _) =
      B.fromText (modify_open begin)
        `mappend` B.fromText ">"
        `mappend` attrs
        `mappend` B.fromText "{}"
    go attrs (CustomLeaf tag close _) =
      B.fromText "\\<html:"
        `mappend` fromChoiceString d tag
        `mappend` attrs
        `mappend` B.fromText ">{}"
    go attrs (AddAttribute _ key value h) =
      go
        ( B.singleton '['
            `mappend` B.fromText (modify_key key)
            `mappend` B.fromText "]{"
            `mappend` wrap_verb (fromChoiceString d value)
            `mappend` B.fromText "}"
            `mappend` attrs
        )
        h
    go attrs (AddCustomAttribute key value h) =
      go
        ( B.singleton '['
            `mappend` fromChoiceString d key
            `mappend` B.fromText "]{"
            `mappend` wrap_verb (fromChoiceString d value)
            `mappend` B.fromText "}"
            `mappend` attrs
        )
        h
    go _ (Content content _) = wrap_verb (fromChoiceString d content)
    go _ (Comment comment _) =
      B.fromText "% "
        `mappend` fromChoiceString d comment
    go attrs (Append h1 h2) = go attrs h1 `mappend` go attrs h2
    go _ (Empty _) = mempty
    {-# NOINLINE go #-}
{-# INLINE renderMarkupBuilderWith #-}

renderMarkupWith :: (ByteString -> Text) -> Html -> L.Text
renderMarkupWith d = B.toLazyText . renderMarkupBuilderWith d
{-# INLINE renderMarkupWith #-}

renderForesterHtml :: Html -> L.Text
renderForesterHtml = renderMarkupWith decodeUtf8
{-# INLINE renderForesterHtml #-}
