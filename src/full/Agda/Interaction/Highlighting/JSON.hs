
-- | Functions which give precise syntax highlighting info in JSON format.

module Agda.Interaction.Highlighting.JSON (jsonifyHighlightingInfo) where

import Agda.Interaction.Highlighting.Common
import Agda.Interaction.Highlighting.Precise hiding (String)
import Agda.Interaction.Highlighting.Range (Range(..))
import Agda.Interaction.Response
import Agda.TypeChecking.Monad (HighlightingMethod(..), ModuleToSource)
import Agda.Utils.FileName (filePath)
import Agda.Utils.IO.TempFile (writeToTempFile)

import Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Map as Map

import Agda.Utils.Impossible

-- | Encode meta information into a JSON Value
showAspects
  :: ModuleToSource
     -- ^ Must contain a mapping for the definition site's module, if any.
  -> (Range, Aspects) -> Value
showAspects modFile (range, aspect) = object
  [ "range" .= [from range, to range]
  , "atoms" .= toAtoms aspect
  , "tokenBased" .= tokenBased aspect
  , "note" .= note aspect
  , "definitionSite" .= fmap defSite (definitionSite aspect)
  ]
  where
    defSite (DefinitionSite mdl position _ _) = object
      [ "filepath" .= filePath (Map.findWithDefault __IMPOSSIBLE__ mdl modFile)
      , "position" .= position
      ]

instance ToJSON TokenBased where
    toJSON TokenBased = String "TokenBased"
    toJSON NotOnlyTokenBased = String "NotOnlyTokenBased"

-- | Turns syntax highlighting information into a JSON value
jsonifyHighlightingInfo
  :: HighlightingInfo
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
      , "payload" .= map (showAspects modFile) (ranges info)
      ]

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
