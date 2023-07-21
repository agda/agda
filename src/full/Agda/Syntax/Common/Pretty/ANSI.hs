module Agda.Syntax.Common.Pretty.ANSI where
import Control.Monad.IO.Class
import Control.Monad

import Text.PrettyPrint.Annotated.HughesPJ (renderDecoratedM)

import Agda.Interaction.Options.HasOptions
import Agda.Interaction.Options.Base
import Agda.Syntax.Common.Aspect
import Agda.Syntax.Common.Pretty
import Agda.Utils.Monad

import System.Console.ANSI
import System.IO

-- | Render an annotated, pretty-printing 'Doc'ument into a string
-- suitable for printing on VT100-compatible terminals.
renderAnsiIO :: Doc -> IO ()
renderAnsiIO = renderDecoratedM start end putStr (putStr "\n") where
  start = maybe mempty (setSGR . aspSGR) . aspect
  end _ = setSGR [Reset]

  aspSGR :: Aspect -> [SGR]
  aspSGR String        = [SetColor Foreground Dull Red]
  aspSGR Number        = [SetColor Foreground Dull Magenta]
  aspSGR PrimitiveType = [SetColor Foreground Dull Blue]
  aspSGR (Name (Just nk) _) = case nk of
    Bound                   -> []
    Generalizable           -> []
    Argument                -> []

    Constructor Inductive   -> [SetColor Foreground Dull Green]
    Constructor CoInductive -> [SetColor Foreground Dull Green]

    Field                   -> [SetColor Foreground Vivid Magenta]

    Module                  -> [SetColor Foreground Vivid Magenta]

    Function                -> [SetColor Foreground Dull Blue]
    Postulate               -> [SetColor Foreground Dull Blue]
    Datatype                -> [SetColor Foreground Dull Blue]
    Record                  -> [SetColor Foreground Dull Blue]
    Primitive               -> [SetColor Foreground Dull Blue]

    Macro                   -> [SetColor Foreground Dull Cyan]
  aspSGR _ = []

putDoc :: (MonadIO m, HasOptions m) => Doc -> m ()
putDoc doc = do
  outputcol <- liftIO (hSupportsANSI stdout)
  wantscol <- commandLineOptions
  let
    col = case optDiagnosticsColour wantscol of
      AutoColour   -> outputcol
      AlwaysColour -> True
      NeverColour  -> False

  liftIO $ if col
    then renderAnsiIO doc
    else putStrLn (render doc)
