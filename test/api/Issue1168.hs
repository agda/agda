{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}

module Main where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import System.Exit            ( exitSuccess )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Interaction.Imports        ( readInterface )
import Agda.Interaction.Options        ( defaultOptions )
import Agda.TypeChecking.Monad.Base    ( Interface, runTCMTop, TCErr )
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions )

------------------------------------------------------------------------------

main ∷ IO ()
main = do
  r ∷ Either TCErr (Maybe Interface) ← liftIO $ runTCMTop $
    do setCommandLineOptions defaultOptions
       readInterface "Issue1168.agdai"

  case r of
    Right (Just _) → exitSuccess

    -- This case can occurs because:
    --
    -- a) there is an issue with the Agda interface files or
    --
    -- b) the Agda versions used for compiling Issue1168.hs and
    -- type-checking Issue1168.agda are different.
    Right Nothing → error "Nothing"

    -- Impossible.
    Left _ → error "Left"
