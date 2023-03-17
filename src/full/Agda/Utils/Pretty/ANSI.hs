{-# LANGUAGE CPP #-}
module Agda.Utils.Pretty.ANSI where

import Control.Monad.IO.Class
import Control.Monad

import Text.PrettyPrint.Annotated.HughesPJ (renderDecorated)

import Agda.Interaction.Options.HasOptions
import Agda.Interaction.Options.Base
import Agda.Utils.Pretty.Aspect
import Agda.Utils.Pretty
import Agda.Utils.Monad

#ifdef HAS_ISATTY
import System.Posix.Terminal
import System.Posix.IO
#endif

-- | Render an annotated, pretty-printing 'Doc'ument into a string
-- suitable for printing on VT100-compatible terminals.
renderAnsiTerminal :: Doc -> String
renderAnsiTerminal = renderDecorated (maybe mempty aspSGR . aspect) (maybe mempty (const reset) . aspect) where
  reset :: String
  reset = "\x1b[0m"

  red, green, yellow, blue, magenta, cyan :: String
  [red, green, yellow, blue, magenta, cyan] = map (\c -> "\x1b[" ++ show c ++ "m") [31..36]

  aspSGR :: Aspect -> String
  aspSGR String        = red
  aspSGR Number        = magenta
  aspSGR PrimitiveType = cyan
  aspSGR (Name (Just nk) _) = case nk of
    Bound                   -> ""
    Generalizable           -> ""
    Argument                -> ""

    Constructor Inductive   -> green
    Constructor CoInductive -> green

    Field                   -> magenta

    Module                  -> magenta

    Function                -> blue
    Postulate               -> blue
    Datatype                -> blue
    Record                  -> blue
    Primitive               -> blue

    Macro                   -> cyan
  aspSGR _ = ""

stdoutHasColours :: MonadIO m => m Bool
#if defined(HAS_ISATTY)
stdoutHasColours = liftIO $ queryTerminal stdOutput

#else

stdoutHasColours = pure False
#endif

putDoc :: (MonadIO m, HasOptions m) => Doc -> m ()
putDoc doc = do
  outputcol <- stdoutHasColours
  wantscol <- commandLineOptions
  let
    col = case optDiagnosticsColour wantscol of
      AutoColour   -> outputcol
      AlwaysColour -> True
      NeverColour  -> False

  liftIO . putStr $ if col
    then renderAnsiTerminal doc
    else render doc
