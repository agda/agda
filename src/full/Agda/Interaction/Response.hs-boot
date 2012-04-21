module Agda.Interaction.Response
  ( InteractionOutputCallback
  , defaultInteractionOutputCallback
  ) where

data Response

type InteractionOutputCallback = Response -> IO ()
defaultInteractionOutputCallback :: InteractionOutputCallback
