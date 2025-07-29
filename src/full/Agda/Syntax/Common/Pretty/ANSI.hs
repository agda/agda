{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds #-}

module Agda.Syntax.Common.Pretty.ANSI where

import Control.Monad.IO.Class ( MonadIO(..) )
import qualified Data.Text as Text

import Text.PrettyPrint.Annotated.HughesPJ ( renderDecoratedM )

import Agda.Interaction.Options.HasOptions ( HasOptions(commandLineOptions) )
import Agda.Interaction.Options.Base
import Agda.Syntax.Common.Aspect as Aspect
import Agda.Syntax.Common.Pretty ( render, Doc )

import System.Console.ANSI
import System.Console.ANSI.Codes ( osc )
import System.IO ( stdout )

-- | Render an annotated, pretty-printing 'Doc'ument into a string
-- suitable for printing on VT100-compatible terminals.
renderAnsiIO :: Doc -> IO ()
renderAnsiIO = renderDecoratedM start end putStr (putStr "\n")
  where
    start ann = maybe mempty (\ a -> setSGR (aspSGR a) <> startIO a) $ aspect ann
    end   ann = maybe mempty endIO (aspect ann) <> setSGR [Reset]

    -- Andreas, 2025-07-28
    -- ansi-terminal has no good interface for hyperlinks in the start/end style,
    -- so we have to implement this manually here, breaking the abstraction.
    startIO :: Aspect -> IO ()
    startIO = \case
      URL ref -> putStr $ osc "8" (";" ++ Text.unpack ref)
      _ -> return ()

    endIO :: Aspect -> IO ()
    endIO = \case
      URL _ -> putStr $ osc "8" ";"
      _ -> return ()

    aspSGR :: Aspect -> [SGR]
    aspSGR = \case
      URL _url      -> [SetUnderlining SingleUnderline]
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
