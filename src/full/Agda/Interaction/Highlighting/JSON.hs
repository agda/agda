{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Functions which give precise syntax highlighting info in JSON format.

module Agda.Interaction.Highlighting.JSON (jsonifyHighlightingInfo) where

import Agda.Interaction.Highlighting.Precise hiding (String)
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.EmacsCommand
import Agda.Interaction.Response
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
  (TCM, envHighlightingMethod, HighlightingMethod(..), ModuleToSource)
import Agda.Utils.FileName
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.String

import qualified Control.Exception as E
import Control.Monad.Reader
import Data.Aeson
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Char
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified System.Directory as D
import qualified System.IO as IO

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Read/show functions

-- | Converts the 'aspect' and 'otherAspects' fields to atoms
toAtoms :: Aspects -> [String]
toAtoms m = map toAtom (otherAspects m) ++ toAtoms' (aspect m)
  where
  toAtom :: Show a => a -> String
  toAtom = map toLower . show

  kindToAtom (Constructor Inductive)   = "inductiveconstructor"
  kindToAtom (Constructor CoInductive) = "coinductiveconstructor"
  kindToAtom k                         = toAtom k

  toAtoms' Nothing               = []
  toAtoms' (Just (Name mKind op)) =
    map kindToAtom (maybeToList mKind) ++ opAtom
    where opAtom | op        = ["operator"]
                 | otherwise = []
  toAtoms' (Just a) = [toAtom a]

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
jsonifyHighlightingInfo info remove method modFile = do
  case ranges info of
    _             | method == Direct                   -> direct
    ((_, mi) : _) | otherAspects mi == [TypeChecks] ||
                    mi == mempty                       -> direct
    _                                                  -> indirect
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
      dir      <- D.getTemporaryDirectory
      filepath <- E.bracket (IO.openTempFile dir "agda2-mode") (IO.hClose . snd) $ \ (filepath, handle) -> do
        UTF8.hPutStr handle (BS.unpack (encode result))
        return filepath
      return $ object
        [ "kind"     .= String "HighlightingInfo"
        , "direct"   .= False
        , "filepath" .= filepath
        ]
