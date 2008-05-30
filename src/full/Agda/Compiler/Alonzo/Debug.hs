module Agda.Compiler.Alonzo.Debug where

import Control.Monad.State

import Agda.Interaction.Monad
import Agda.TypeChecking.Monad

import Data.Generics
import Data.Generics.Text
import Data.Map

-- import Debug.Trace
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Pretty
import Text.PrettyPrint

import System.IO

-- --------------------------------
-- DEBUG INFO

debugMsg :: String -> IM()
debugMsg msg = liftIO $ hPutStrLn stderr msg

debugData :: Data a => a -> IM()
debugData = debugMsg . gshow

debugSigInfo :: Signature -> IM()
debugSigInfo sig = do
  mapM_ debugData (keys sig)
--  mapM_ (debugMsg . show) (keys sig)

-- instance Show ModuleName where
--    show (MName id c) = show c