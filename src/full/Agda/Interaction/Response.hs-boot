module Agda.Interaction.Response
  ( InteractionOutputCallback
  , defaultInteractionOutputCallback
  , Response
  ) where

import {-# SOURCE #-} Agda.TypeChecking.Monad.Base

data Response

type InteractionOutputCallback = Response -> TCM ()
defaultInteractionOutputCallback :: InteractionOutputCallback
