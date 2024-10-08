{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.MAlonzo.Pragmas where

import Control.Monad.Trans.Maybe

import Data.Maybe
import Data.Char
import qualified Data.List as List
import qualified Data.Map as Map
import Text.ParserCombinators.ReadP

import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Primitive

import Agda.Compiler.MAlonzo.Misc

import Agda.Syntax.Common.Pretty hiding (char)
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.String ( ltrim )
import Agda.Utils.Three

import Agda.Utils.Impossible

type HaskellCode = String
type HaskellType = String

-- | GHC backend translation pragmas.
data HaskellPragma
  = HsDefn Range HaskellCode
      --  ^ @COMPILE GHC x = <code>@
  | HsType Range HaskellType
      --  ^ @COMPILE GHC X = type <type>@
  | HsData Range HaskellType [HaskellCode]
      -- ^ @COMPILE GHC X = data D (c₁ | ... | cₙ)
  | HsExport Range HaskellCode
      -- ^ @COMPILE GHC x as f@
  deriving (Show, Eq)

instance HasRange HaskellPragma where
  getRange (HsDefn   r _)   = r
  getRange (HsType   r _)   = r
  getRange (HsData   r _ _) = r
  getRange (HsExport r _)   = r

instance Pretty HaskellPragma where
  pretty = \case
    HsDefn   _r hsCode        -> equals <+> text hsCode
    HsType   _r hsType        -> equals <+> text hsType
    HsData   _r hsType hsCons -> hsep $
      [ equals, "data", text hsType
      , parens $ hsep $ map text $ List.intersperse "|" hsCons
      ]
    HsExport _r hsCode        -> "as" <+> text hsCode

-- | Retrieve and parse a @COMPILE GHC@ pragma stored for a name.
--
getHaskellPragma :: QName -> TCM (Maybe HaskellPragma)
getHaskellPragma q = runMaybeT do
  p <- MaybeT $ getUniqueCompilerPragma ghcBackendName q
  setCurrentRange p do
    pragma <- MaybeT $ parseHaskellPragma p
    MaybeT $ sanityCheckPragma q pragma

-- Syntax for Haskell pragmas:
--  HsDefn CODE       "= CODE"
--  HsType TYPE       "= type TYPE"
--  HsData NAME CONS  "= data NAME (CON₁ | .. | CONₙ)"
--  HsExport NAME     "as NAME"
parsePragma :: CompilerPragma -> Maybe HaskellPragma
parsePragma (CompilerPragma r s) =
  case [ p | (p, "") <- readP_to_S pragmaP s ] of
    []  -> Nothing
    [p] -> Just p
    ps  -> -- shouldn't happen
           -- trace ("Ambiguous parse of pragma '" ++ s ++ "':\n" ++ unlines (map show ps)) $
           __IMPOSSIBLE__
  where
    pragmaP :: ReadP HaskellPragma
    pragmaP = choice [ exportP, typeP, dataP, defnP ]

    whitespace = many1 (satisfy isSpace)

    wordsP []     = return ()
    wordsP (w:ws) = skipSpaces *> string w *> wordsP ws

    barP = skipSpaces *> char '|'

    -- quite liberal
    isIdent c = isAlphaNum c || elem c ("_.':[]" :: String)
    isOp c    = not $ isSpace c || elem c ("()" :: String)
    hsIdent = fst <$> gather (choice
                [ string "()"
                , many1 (satisfy isIdent)
                , between (char '(') (char ')') (many1 (satisfy isOp))
                ])
    hsCode  = many1 get -- very liberal

    paren = between (skipSpaces *> char '(') (skipSpaces *> char ')')

    isPrefixSpaceOf pre s = case List.stripPrefix pre s of
      Just (x:_) -> isSpace x
      _ -> False

    notTypeOrData = do
      s <- look
      guard $ not $ any (`isPrefixSpaceOf` s) ["type", "data"]

    exportP = HsExport r <$ wordsP ["as"]        <* whitespace <*> hsIdent <* skipSpaces
    typeP   = HsType   r <$ wordsP ["=", "type"] <* whitespace <*> hsCode
    dataP   = HsData   r <$ wordsP ["=", "data"] <* whitespace <*> hsIdent <*>
                                                    paren (sepBy (skipSpaces *> hsIdent) barP) <* skipSpaces
    defnP   = HsDefn   r <$ wordsP ["="]         <* whitespace <*  notTypeOrData <*> hsCode

parseHaskellPragma :: CompilerPragma -> TCM (Maybe HaskellPragma)
parseHaskellPragma p@(CompilerPragma _ s) = do
  let p' = parsePragma p
  () <- whenNothing p' $ warning $ PragmaCompileUnparsable s
  return p'

-- | Check whether the parsed @COMPILE GHC@ pragma matches the kind of identifier it attaches to.
--
sanityCheckPragma :: QName -> HaskellPragma -> TCM (Maybe HaskellPragma)
sanityCheckPragma x pragma = do
  reportSLn "compile.haskell.pragma" 40 $ unwords ["sanityCheckPragma" , prettyShow x]
  def <- getConstInfo x
  case pragma of

    HsDefn{} -> case theDef def of
      Axiom{}        -> ok
      Function{}     -> notBuiltinFlat
      AbstractDefn{} -> __IMPOSSIBLE__
      Datatype{}     -> recOrDataErr "data"
      Record{}       -> recOrDataErr "record"
      _ -> bad "Haskell definitions can only be given for postulates and functions."

    HsData{} -> case theDef def of
      Datatype{} -> ok
      Record{}   -> ok
      _ -> bad "Haskell data types can only be given for data or record types."

    HsType{} -> case theDef def of
      Axiom{}    -> ok
      Datatype{} -> do
        -- We use HsType pragmas for Nat, Int and Bool
        ifM (flip anyM ((Just (defName def) ==) <.> getBuiltinName) [builtinNat, builtinInteger, builtinBool])
          {-then-} ok
          {-else-} notPostulate
      _ -> notPostulate

    HsExport{} -> case theDef def of
      Function{} -> notBuiltinFlat
      _ -> bad "Only functions can be exported to Haskell using {-# COMPILE GHC <Name> as <HsName> #-}"

  where
    ok  = return $ Just pragma
    bad = (Nothing <$) . warning . PragmaCompileWrong x
    recOrDataErr which = bad $ unwords
      [ "Bad COMPILE GHC pragma for", which, "type. Use"
      , "{-# COMPILE GHC <Name> = data <HsData> (<HsCon1> | .. | <HsConN>) #-}"
      ]
    notPostulate = bad "Haskell types can only be given for postulates."
    notBuiltinFlat = do
      mflat <- getBuiltinName builtinFlat
      reportSLn "compile.haskell.pragma" 40 $ render $ vcat
        [ "Checking pragma for FLAT"
        , hsep [ "x     =", pretty x ]
        , hsep [ "mflat =", pretty mflat ]
        ]
      if Just x == mflat
        then bad "COMPILE GHC pragmas are not allowed for the FLAT builtin."
        else ok


-- TODO: cache this to avoid parsing the pragma for every constructor
--       occurrence!
getHaskellConstructor :: QName -> HsCompileM (Maybe HaskellCode)
getHaskellConstructor c = do
  c    <- canonicalName c
  cDef <- theDef <$> getConstInfo c
  env  <- askGHCEnv
  let is c p = Just c == p env
  case cDef of
    _ | c `is` ghcEnvTrue    -> return $ Just "True"
      | c `is` ghcEnvFalse   -> return $ Just "False"
      | c `is` ghcEnvNil     -> return $ Just "[]"
      | c `is` ghcEnvCons    -> return $ Just "(:)"
      | c `is` ghcEnvNothing -> return $ Just "Nothing"
      | c `is` ghcEnvJust    -> return $ Just "Just"
      | c `is` ghcEnvSharp   -> return $ Just "MAlonzo.RTE.Sharp"
      | c `is` ghcEnvIZero   -> return $ Just "False"
      | c `is` ghcEnvIOne    -> return $ Just "True"
    Constructor{conData = d} -> do
      mp <- liftTCM $ getHaskellPragma d
      case mp of
        Just (HsData _ _ hsCons) -> do
          cons <- defConstructors . theDef <$> getConstInfo d
          return $ Just $ fromMaybe __IMPOSSIBLE__ $ lookup c $ zip cons hsCons
        _ -> return Nothing
    _ -> return Nothing

-- | Get content of @FOREIGN GHC@ pragmas, sorted by 'KindOfForeignCode':
--   file header pragmas, import statements, rest.
foreignHaskell :: Interface -> ([String], [String], [String])
foreignHaskell = partitionByKindOfForeignCode classifyForeign
    . map getCode . maybe [] (reverse . getForeignCodeStack) . Map.lookup ghcBackendName . iForeignCode
  where getCode (ForeignCode _ code) = code

-- | Classify @FOREIGN@ Haskell code.
data KindOfForeignCode
  = ForeignFileHeaderPragma
      -- ^ A pragma that must appear before the module header.
  | ForeignImport
      -- ^ An import statement.  Must appear right after the module header.
  | ForeignOther
      -- ^ The rest.  To appear after the import statements.

-- | Classify a @FOREIGN GHC@ declaration.
classifyForeign :: String -> KindOfForeignCode
classifyForeign s0 = case ltrim s0 of
  s | "import " `List.isPrefixOf` s -> ForeignImport
  s | "{-#" `List.isPrefixOf` s -> classifyPragma $ drop 3 s
  _ -> ForeignOther

-- | Classify a Haskell pragma into whether it is a file header pragma or not.
classifyPragma :: String -> KindOfForeignCode
classifyPragma s0 = case ltrim s0 of
  s | any (`List.isPrefixOf` s) fileHeaderPragmas -> ForeignFileHeaderPragma
  _ -> ForeignOther
  where
  fileHeaderPragmas =
    [ "LANGUAGE"
    , "OPTIONS_GHC"
    , "INCLUDE"
    ]

-- | Partition a list by 'KindOfForeignCode' attribute.
partitionByKindOfForeignCode :: (a -> KindOfForeignCode) -> [a] -> ([a], [a], [a])
partitionByKindOfForeignCode f = partition3 $ toThree . f
  where
  toThree = \case
    ForeignFileHeaderPragma -> One
    ForeignImport           -> Two
    ForeignOther            -> Three
