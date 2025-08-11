{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds #-}

module Agda.Syntax.Common.Pretty.ANSI ( printTreeAnsi, putDocLn, putDocTree, putDocTreeLn ) where

import Control.Monad.IO.Class ( MonadIO(..) )
import Data.Functor ((<&>))
import Data.Text    qualified as Text
import Data.Text.IO qualified as Text

import System.Console.ANSI
import System.Console.ANSI.Codes ( osc )
import System.IO ( stdout )

-- UNUSED:
-- import Text.PrettyPrint.Annotated.HughesPJ ( renderDecoratedM )

import Agda.Interaction.Options.HasOptions ( HasOptions(commandLineOptions) )
import Agda.Interaction.Options.Base

import Agda.Syntax.Common.Aspect as Aspect
import Agda.Syntax.Common.Pretty ( Doc, DocTree )

import Agda.Utils.DocTree (renderTree', renderToTree, treeToTextNoAnn)

-- | Print an annotated, pretty-printing 'DocTree' onto a VT100-compatible terminal.
printTreeAnsi :: DocTree -> IO ()
printTreeAnsi = renderTree' Text.putStr \ ann t -> startAnn ann <> t <> endAnn ann

startAnn :: Aspects -> IO ()
startAnn ann = maybe mempty (\ a -> setSGR (aspSGR a) <> startIO a) $ aspect ann

endAnn :: Aspects -> IO ()
endAnn ann = maybe mempty endIO (aspect ann) <> setSGR [Reset]

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

-- UNUSED:
-- -- | Render an annotated, pretty-printing 'Doc'ument to a VT100-compatible terminal.
-- renderAnsiIO :: Doc -> IO ()
-- renderAnsiIO = renderDecoratedM startAnn endAnn putStr (putStr "\n")

putDocTree :: (MonadIO m, HasOptions m) => DocTree -> m ()
putDocTree doc = do
  col <- commandLineOptions <&> optDiagnosticsColour >>= \case
    AutoColour   -> liftIO (hSupportsANSI stdout)
    AlwaysColour -> pure True
    NeverColour  -> pure False

  liftIO do
    if col
      then printTreeAnsi doc
      else Text.putStr (treeToTextNoAnn doc)

putDocTreeLn :: (MonadIO m, HasOptions m) => DocTree -> m ()
putDocTreeLn doc = do
  putDocTree doc
  liftIO $ putStr "\n"

putDoc :: (MonadIO m, HasOptions m) => Doc -> m ()
putDoc = putDocTree . renderToTree

putDocLn :: (MonadIO m, HasOptions m) => Doc -> m ()
putDocLn doc = do
  putDoc doc
  liftIO $ putStr "\n"
