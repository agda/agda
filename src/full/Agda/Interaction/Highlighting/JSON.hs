
-- | Functions which give precise syntax highlighting info in JSON format.

module Agda.Interaction.Highlighting.JSON (jsonifyHighlightingInfo) where

import Agda.Interaction.Highlighting.Common
import Agda.Interaction.Highlighting.Precise hiding (String)
import Agda.Interaction.Highlighting.Range (Range(..), Ranges)
import Agda.Interaction.JSON
import Agda.Interaction.Response
import Agda.TypeChecking.Monad (HighlightingMethod(..), ModuleToSource)
import Agda.Utils.FileName (filePath)
import Agda.Utils.IO.TempFile (writeToTempFile)

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Map as Map
import Data.Maybe

import Agda.Utils.Impossible

-- | Encode meta information into a JSON Value
showAspects
  :: Bool
     -- ^ Only generate a result when there is some relevant data.
  -> ModuleToSource
     -- ^ Must contain a mapping for the definition site's module, if any.
  -> (Range, Aspects)
  -> Maybe Value
showAspects skipEmpty modFile (range, aspects)
  | skipEmpty && noInfo = Nothing
  | otherwise           = Just $ object
    [ "range" .= [from range, to range]
    , "atoms" .= toAtoms aspects
    , "tokenBased" .= tokenBased aspects
    , "note" .= note aspects
    , "definitionSite" .= defSite
    ]
  where
  defSite = case definitionSite aspects of
    Nothing                                     -> Nothing
    Just (DefinitionSite mdl position _ _ link) ->
      if not link
      then Nothing
      else Just $ object
        [ "filepath" .=
            filePath (Map.findWithDefault __IMPOSSIBLE__ mdl modFile)
        , "position" .= position
        ]

  noInfo =
    isNothing (aspect aspects) &&
    null (otherAspects aspects) &&
    isNothing defSite

instance EncodeTCM TokenBased where
instance ToJSON TokenBased where
    toJSON TokenBased = String "TokenBased"
    toJSON NotOnlyTokenBased = String "NotOnlyTokenBased"

-- | Turns syntax highlighting information into a JSON value
jsonifyHighlightingInfo
  :: Either Ranges HighlightingInfo
     -- ^ @'Left' rs@: Remove highlighting from the ranges @rs@.
  -> RemoveTokenBasedHighlighting
  -> HighlightingMethod
  -> ModuleToSource
     -- ^ Must contain a mapping for every definition site's module.
  -> IO Value
jsonifyHighlightingInfo info remove method modFile =
  case chooseHighlightingMethod info method of
    Direct   -> direct
    Indirect -> indirect
  where
    result :: Value
    result = object
      [ "remove" .= case remove of
          RemoveHighlighting -> True
          KeepHighlighting -> False
      , "payload" .=
          catMaybes (map (showAspects skipEmpty modFile) (toList info'))
      ]
      where
      (skipEmpty, info') = case info of
        Right info -> (True,  info)
        Left rs    -> (False, singleton rs mempty)

    direct :: IO Value
    direct = return $ object
      [ "kind"   .= String "HighlightingInfo"
      , "direct" .= True
      , "info"   .= result
      ]

    indirect :: IO Value
    indirect = do
      filepath <- writeToTempFile (BS.unpack (encode result))
      return $ object
        [ "kind"     .= String "HighlightingInfo"
        , "direct"   .= False
        , "filepath" .= filepath
        ]
