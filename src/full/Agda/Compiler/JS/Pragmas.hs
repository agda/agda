module Agda.Compiler.JS.Pragmas where

import Agda.Compiler.JS.Pretty (isValidJSIdent)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Position
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Data.Maybe (mapMaybe)
import GHC.Unicode
import Text.ParserCombinators.ReadP

type JavaScriptCode = String

--  ^ @COMPILE JS x as f@
data JsExportPragma = JsExport Range JavaScriptCode
  deriving (Show, Eq)

instance HasRange JsExportPragma where
  getRange (JsExport r _) = r

--  ^ @COMPILE JS x = <code>@
data JsDefnPragma = JsDefn Range JavaScriptCode
  deriving (Show, Eq)

instance HasRange JsDefnPragma where
  getRange (JsDefn r _) = r

data JsPragmaChoice
  = JsExportChoice JsExportPragma
  | JsDefnChoice JsDefnPragma
  deriving (Show, Eq)

instance HasRange JsPragmaChoice where
  getRange (JsExportChoice p) = getRange p
  getRange (JsDefnChoice p) = getRange p

-- | JS backend translation pragmas.
data JavaScriptPragma = JavaScriptPragma
  { export :: Maybe JsExportPragma,
    defn :: Maybe JsDefnPragma
  }
  deriving (Show, Eq)

parsePragma :: CompilerPragma -> Either String JsPragmaChoice
parsePragma (CompilerPragma r s) =
  case [p | (p, "") <- readP_to_S pragmaP s] of
    [] -> Left $ "Failed to parse JS pragma '" ++ s ++ "'"
    [p] -> Right p
    ps -> Left $ "Ambiguous parse of pragma '" ++ s ++ "':\n" ++ unlines (map show ps) -- shouldn't happen
  where
    pragmaP :: ReadP JsPragmaChoice
    pragmaP = choice [exportP, defnP]

    whitespace = many1 (satisfy isSpace)

    wordsP [] = return ()
    wordsP (w : ws) = skipSpaces *> string w *> wordsP ws

    isIdent = isValidJSIdent . pure
    jsIdent = fst <$> gather (many1 (satisfy isIdent))

    jsCode = many1 get

    exportP = JsExportChoice . JsExport r <$ wordsP ["as"] <* whitespace <*> jsIdent <* skipSpaces
    defnP = JsDefnChoice . JsDefn r <$ wordsP ["="] <* whitespace <*> jsCode

parseJavaScriptPragma :: (MonadTCError m, MonadTrace m) => CompilerPragma -> m JsPragmaChoice
parseJavaScriptPragma p = setCurrentRange p $
  case parsePragma p of
    Left err -> genericError err
    Right p -> return p

getUniquePragmaType :: (HasRange a, MonadTCError m, MonadTrace m) => QName -> (JsPragmaChoice -> Maybe a) -> [JsPragmaChoice] -> m (Maybe a)
getUniquePragmaType q f ps = case mapMaybe f ps of
  [] -> return Nothing
  [p] -> return $ Just p
  (_ : p1 : _) ->
    setCurrentRange p1 $
      genericDocError =<< do
        hang (text ("Conflicting JS pragmas for") <+> pretty q <+> (text "at")) 2 $
          vcat [(text "-") <+> pretty (getRange p) | p <- ps]

getJavaScriptPragma :: QName -> TCM JavaScriptPragma
getJavaScriptPragma q = do
  def <- getConstInfo q
  pragmas <- traverse parseJavaScriptPragma $ defCompilerPragmas jsBackendName def
  export <- getUniquePragmaType q chooseExportPragma pragmas
  defn <- getUniquePragmaType q chooseDefnPragma pragmas

  -- setCurrentRange pragma $ pragma <$ sanityCheckPragma def pragma
  return $ JavaScriptPragma {export, defn}
  where
    chooseExportPragma :: JsPragmaChoice -> Maybe JsExportPragma
    chooseExportPragma (JsDefnChoice _) = Nothing
    chooseExportPragma (JsExportChoice p) = Just p

    chooseDefnPragma :: JsPragmaChoice -> Maybe JsDefnPragma
    chooseDefnPragma (JsDefnChoice p) = Just p
    chooseDefnPragma (JsExportChoice _) = Nothing

-- sanityCheckPragma :: (HasBuiltins m, MonadTCError m, MonadReduce m) => Definition -> Maybe JavaScriptPragma -> m ()
-- -- sanityCheckPragma _ Nothing = return ()
-- -- sanityCheckPragma _ (Just JsDefn {}) = return ()
-- -- sanityCheckPragma _ (Just JsExport {}) = return ()
-- sanityCheckPragma _ _ = return ()
