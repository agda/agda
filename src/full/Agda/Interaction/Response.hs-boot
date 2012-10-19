module Agda.Interaction.Response
  ( InteractionOutputCallback
  , defaultInteractionOutputCallback
  ) where

import {-# SOURCE #-} Agda.TypeChecking.Monad.Base

data Response

type InteractionOutputCallback = Response -> TCM ()
defaultInteractionOutputCallback :: InteractionOutputCallback
