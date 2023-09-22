{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.MAlonzo.Pragmas where

import Control.Monad
import Data.Maybe
import Data.Char
import qualified Data.List as List
import qualified Data.Map as Map
import Text.ParserCombinators.ReadP

import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive

import Agda.Syntax.Common.Pretty hiding (char)
import Agda.Utils.String ( ltrim )
import Agda.Utils.Three

import Agda.Compiler.MAlonzo.Misc

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

-- Syntax for Haskell pragmas:
--  HsDefn CODE       "= CODE"
--  HsType TYPE       "= type TYPE"
--  HsData NAME CONS  "= data NAME (CON₁ | .. | CONₙ)"
--  HsExport NAME     "as NAME"
parsePragma :: CompilerPragma -> Either String HaskellPragma
parsePragma (CompilerPragma r s) =
  case [ p | (p, "") <- readP_to_S pragmaP s ] of
    []  -> Left $ "Failed to parse GHC pragma '" ++ s ++ "'"
    [p] -> Right p
    ps  -> Left $ "Ambiguous parse of pragma '" ++ s ++ "':\n" ++ unlines (map show ps)  -- shouldn't happen
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

parseHaskellPragma :: (MonadTCError m, MonadTrace m) => CompilerPragma -> m HaskellPragma
parseHaskellPragma p = setCurrentRange p $
  case parsePragma p of
    Left err -> genericError err
    Right p  -> return p

getHaskellPragma :: QName -> TCM (Maybe HaskellPragma)
getHaskellPragma q = do
  pragma <- traverse parseHaskellPragma =<< getUniqueCompilerPragma ghcBackendName q
  def <- getConstInfo q
  setCurrentRange pragma $ pragma <$ sanityCheckPragma def pragma

sanityCheckPragma :: (HasBuiltins m, MonadTCError m, MonadReduce m) => Definition -> Maybe HaskellPragma -> m ()
sanityCheckPragma _ Nothing = return ()
sanityCheckPragma def (Just HsDefn{}) =
  case theDef def of
    Axiom{}        -> return ()
    Function{}     -> return ()
    AbstractDefn{} -> __IMPOSSIBLE__
    Datatype{}     -> recOrDataErr "data"
    Record{}       -> recOrDataErr "record"
    _              -> typeError $ GenericError "Haskell definitions can only be given for postulates and functions."
    where
      recOrDataErr which =
        typeError $ GenericDocError $
          sep [ text $ "Bad COMPILE GHC pragma for " ++ which ++ " type. Use"
              , "{-# COMPILE GHC <Name> = data <HsData> (<HsCon1> | .. | <HsConN>) #-}" ]
sanityCheckPragma def (Just HsData{}) =
  case theDef def of
    Datatype{} -> return ()
    Record{}   -> return ()
    _          -> typeError $ GenericError "Haskell data types can only be given for data or record types."
sanityCheckPragma def (Just HsType{}) =
  case theDef def of
    Axiom{} -> return ()
    Datatype{} -> do
      -- We use HsType pragmas for Nat, Int and Bool
      nat  <- getBuiltinName builtinNat
      int  <- getBuiltinName builtinInteger
      bool <- getBuiltinName builtinBool
      unless (Just (defName def) `elem` [nat, int, bool]) err
    _ -> err
  where
    err = typeError $ GenericError "Haskell types can only be given for postulates."
sanityCheckPragma def (Just HsExport{}) =
  case theDef def of
    Function{} -> return ()
    _ -> typeError $ GenericError "Only functions can be exported to Haskell using {-# COMPILE GHC <Name> as <HsName> #-}"



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
