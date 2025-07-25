module Agda.Syntax.Common.Pretty.ANSI where
import Control.Monad.IO.Class
import Control.Monad

import Text.PrettyPrint.Annotated.HughesPJ (renderDecoratedM)

import Agda.Interaction.Options.HasOptions
import Agda.Interaction.Options.Base
import Agda.Syntax.Common.Aspect as Aspect
import Agda.Syntax.Common.Pretty
import Agda.Utils.Monad

import System.Console.ANSI
import System.IO

-- | Render an annotated, pretty-printing 'Doc'ument into a string
-- suitable for printing on VT100-compatible terminals.
renderAnsiIO :: Doc -> IO ()
renderAnsiIO = renderDecoratedM start end putStr (putStr "\n")
  where
    start ann = maybe mempty (setSGR . aspSGR) $ aspect ann
    end _ann  = setSGR [Reset]

    aspSGR :: Aspect -> [SGR]
    aspSGR = \case
      String        -> [SetColor Foreground Dull Red]
      Number        -> [SetColor Foreground Dull Magenta]
      PrimitiveType -> [SetColor Foreground Dull Blue]
      Name Nothing _ -> []
      Name (Just nk) _ -> case nk of
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
      Aspect.Background -> []
      Comment           -> []
      Hole              -> []
      Keyword           -> []
      Markup            -> []
      Pragma            -> []
      Symbol            -> []

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
