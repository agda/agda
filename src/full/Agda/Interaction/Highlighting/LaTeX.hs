{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}

-- | Function for generating highlighted and aligned LaTeX from literate
-- Agda source.

module Agda.Interaction.Highlighting.LaTeX
  ( generateLaTeX
  ) where

import Prelude hiding (log)
import Data.Char
import Data.Maybe
import Data.Function
import Control.Monad.RWS
import System.Directory
import System.FilePath
import Data.Text (Text)
import qualified Data.Text          as T
import qualified Data.Text.IO       as T
import qualified Data.Text.Encoding as E
import qualified Data.ByteString    as BS

import qualified Data.IntMap as IntMap
import qualified Data.List   as List

import Paths_Agda

import Agda.Packaging.Base
import Agda.Packaging.Database
import Agda.Syntax.Common
import Agda.Syntax.Concrete (TopLevelModuleName, moduleNameParts)
import qualified Agda.Interaction.FindFile as Find
import Agda.Interaction.Highlighting.Precise
import Agda.TypeChecking.Monad (TCM)
import qualified Agda.TypeChecking.Monad as TCM
import Agda.Interaction.Options
import Agda.Compiler.CallCompiler
import qualified Agda.Utils.IO.UTF8 as UTF8
import Agda.Utils.FileName (filePath)

import Agda.Utils.Except ( ExceptT, MonadError(throwError), runExceptT )

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Datatypes.

-- | The @LaTeX@ monad is a combination of @ExceptT@, @RWST@ and
-- @IO@. The error part is just used to keep track whether we finished
-- or not, the reader part isn't used, the writer is where the output
-- goes and the state is for keeping track of the tokens and some other
-- useful info, and the I/O part is used for printing debugging info.
type LaTeX = ExceptT String (RWST () Text State IO)

data State = State
  { tokens     :: Tokens
  , column     :: Int     -- ^ Column number, used for polytable alignment.
  , indent     :: Int     -- ^ Indentation level, also for alignment.
  , indentPrev :: Int
  , inCode     :: Bool    -- ^ Keeps track of whether we are in a code
                          -- block or not.
  , debugs     :: [Debug] -- ^ Says what debug information should printed.
  }

type Tokens = [Token]

data Token = Token
  { text     :: Text
  , info     :: Aspects
  , position :: Int      -- ^ Is not used currently, but could
                         -- potentially be used for hyperlinks as in
                         -- the HTML output?
  }
  deriving Show

data Debug = MoveColumn | NonCode | Code | Spaces | Output
  deriving (Eq, Show)

-- | Run function for the @LaTeX@ monad.
runLaTeX :: LaTeX a -> () -> State -> IO (Either String a, State, Text)
runLaTeX = runRWST . runExceptT

emptyState :: State
emptyState = State
  { tokens     = []
  , column     = 0
  , indent     = 0
  , indentPrev = 0
  , inCode     = False
  , debugs     = []
  }

------------------------------------------------------------------------
-- * Some helpers.

(<+>) :: Text -> Text -> Text
(<+>) = T.append

isInfixOf' :: Text -> Text -> Maybe (Text, Text)
isInfixOf' needle haystack = go (T.tails haystack) 0
  where
  go []                                         n = Nothing
  go ((T.stripPrefix needle -> Just suf) : xss) n = Just (T.take n haystack, suf)
  go (_                                  : xss) n = go xss (n + 1)

-- Same as above, but starts searching from the back rather than the
-- front.
isInfixOfRev :: Text -> Text -> Maybe (Text, Text)
isInfixOfRev needle haystack
  = case T.reverse needle `isInfixOf'` T.reverse haystack of
      Nothing         -> Nothing
      Just (pre, suf) -> Just (T.reverse suf, T.reverse pre)

isSpaces :: Text -> Bool
isSpaces = T.all isSpace

isActualSpaces :: Text -> Bool
isActualSpaces = T.all (== ' ')

-- | Yields the next token, taking special care to begin/end code
-- blocks. Junk occuring before and after the code blocks is separated
-- into separate tokens, this makes it easier to keep track of whether
-- we are in a code block or not.
nextToken' :: LaTeX Token
nextToken' = do
  toks <- gets tokens
  case toks of
    []     -> throwError "Done"

    -- Clean begin/end code block or a LaTeX comment.
    t : ts | text t == beginCode || text t == endCode ||
             T.singleton '%' == T.take 1 (T.stripStart (text t)) -> do

      modify $ \s -> s { tokens = ts }
      return t

    t : ts -> do
      modify $ \s -> s { tokens = ts }

      inCode <- gets inCode
      let code = if inCode then endCode else beginCode

      case code `isInfixOf'` text t of
        Nothing -> do

          -- Spaces take care of their own column tracking.
          unless (isSpaces (text t)) $ do
            log MoveColumn $ text t
            moveColumn $ T.length $ text t

          return t

        Just (pre, suf) -> do

          let (textToReturn, textsToPutBack) =

               -- This bit fixes issue 954.

               -- Drop spaces up until and including the first trailing
               -- newline after begin code blocks.
               if code == beginCode && isSpaces suf
               then case T.singleton '\n' `isInfixOf'` suf of
                     Nothing        -> (pre, [ beginCode ])
                     Just (_, suf') -> (pre, [ beginCode, suf' ])

               -- Do the converse thing for end code blocks.
               else if code == endCode && isSpaces pre
                    then case T.singleton '\n' `isInfixOfRev` pre of
                           Nothing           -> (code, [ suf ])
                           Just (pre', suf') ->
                             (pre' <+> T.dropWhile (`elem` [' ', '\t']) suf',
                              [ code, suf ])

              -- This case happens for example when you have two code
              -- blocks after each other, i.e. the begin code of the
              -- second ends up in the suffix of the first's end code.
                    else (pre, [ code, suf ])

          let tokToReturn   = t { text = textToReturn }
          let toksToPutBack = map (\txt -> t { text = txt }) textsToPutBack

          unless (isSpaces pre) $ do
            log MoveColumn pre
            moveColumn $ T.length pre

          modify $ \s -> s { tokens = toksToPutBack ++ tokens s }
          return tokToReturn

nextToken :: LaTeX Text
nextToken = text `fmap` nextToken'

resetColumn :: LaTeX ()
resetColumn = modify $ \s -> s { column = 0 }

moveColumn :: Int -> LaTeX ()
moveColumn i = modify $ \s -> s { column = i + column s }

setIndent :: Int -> LaTeX ()
setIndent i = modify $ \s -> s { indent = i }

resetIndent :: LaTeX ()
resetIndent = modify $ \s -> s { indent = 0 }

setIndentPrev :: Int -> LaTeX ()
setIndentPrev i = modify $ \s -> s { indentPrev = i }

resetIndentPrev :: LaTeX ()
resetIndentPrev = modify $ \s -> s { indentPrev = 0 }

setInCode :: LaTeX ()
setInCode = modify $ \s -> s { inCode = True }

unsetInCode :: LaTeX ()
unsetInCode = modify $ \s -> s { inCode = False }

logHelper :: Debug -> Text -> [String] -> LaTeX ()
logHelper debug text extra = do
  debugs <- gets debugs
  when (debug `elem` debugs) $ do
    lift $ lift $ T.putStrLn $ T.pack (show debug ++ ": ") <+>
      T.pack "'" <+> text <+> T.pack "' " <+>
      if null extra
         then T.empty
         else T.pack "(" <+> T.pack (unwords extra) <+> T.pack ")"

log :: Debug -> Text -> LaTeX ()
log MoveColumn text = do
  ind <- gets indent
  logHelper MoveColumn text ["ind=", show ind]
log Code text = do
  ind <- gets indent
  col <- gets column
  logHelper Code text ["ind=", show ind, "col=", show col]
log debug text = logHelper debug text []

log' :: Debug -> String -> LaTeX ()
log' d = log d . T.pack

output :: Text -> LaTeX ()
output text = do
  log Output text
  tell text

------------------------------------------------------------------------
-- * LaTeX and polytable strings.

-- Polytable, http://www.ctan.org/pkg/polytable, is used for code
-- alignment, similar to lhs2TeX's approach.

nl, beginCode, endCode :: Text
nl        = T.pack "%\n"
beginCode = T.pack "\\begin{code}"
endCode   = T.pack "\\end{code}"

ptOpen :: Text
ptOpen = T.pack "\\>"

ptOpen' :: Show a => a -> Text
ptOpen' i = ptOpen <+> T.pack ("[" ++ show i ++ "]")

ptClose :: Text
ptClose = T.pack "\\<"

ptClose' :: Show a => a -> Text
ptClose' i = ptClose <+> T.pack ("[" ++ show i ++ "]")

ptNL :: Text
ptNL = nl <+> T.pack "\\\\\n"

cmdPrefix :: Text
cmdPrefix = T.pack "\\Agda"

cmdArg :: Text -> Text
cmdArg x = T.singleton '{' <+> x <+> T.singleton '}'

cmdIndent :: Show a => a -> Text
cmdIndent i = cmdPrefix <+> T.pack "Indent" <+>
                  cmdArg (T.pack (show i)) <+> cmdArg T.empty

infixl', infix', infixr' :: Text
infixl' = T.pack "infixl"
infix'  = T.pack "infix"
infixr' = T.pack "infixr"

------------------------------------------------------------------------
-- * Automaton.

-- | The start state, @nonCode@, prints non-code (the LaTeX part of
-- literate Agda) until it sees a @beginBlock@.
nonCode :: LaTeX ()
nonCode = do
  tok <- nextToken
  log NonCode tok

  if tok == beginCode

     then do
       output $ beginCode <+> nl
       resetColumn
       setInCode
       code

     else do
       output tok
       nonCode

-- | Deals with code blocks. Every token, except spaces, is pretty
-- printed as a LaTeX command.
code :: LaTeX ()
code = do

  -- Get the column information before grabbing the token, since
  -- grabbing (possibly) moves the column.
  col  <- gets column

  tok' <- nextToken'
  let tok = text tok'
  log Code tok

  when (tok == T.empty) code

  when (col == 0 && not (isActualSpaces tok)) $ do
    output ptOpen

  when (tok == endCode) $ do
    output $ ptClose <+> nl <+> endCode
    unsetInCode
    nonCode

  when (tok `elem` [ infixl', infix', infixr' ]) $ do
    output $ cmdPrefix <+> T.pack "Keyword" <+> cmdArg tok
    fixity
    code

  when (isSpaces tok) $ do
    spaces $ T.group tok
    code

  case aspect (info tok') of
    Nothing -> output $ escape tok
    Just a  -> output $ cmdPrefix <+> T.pack (cmd a) <+> cmdArg (escape tok)

  code

  where
  cmd :: Aspect -> String
  cmd a = let s = show a in case a of
    Comment        -> s
    Keyword        -> s
    String         -> s
    Number         -> s
    Symbol         -> s
    PrimitiveType  -> s
    Name mKind _   -> maybe __IMPOSSIBLE__ showKind mKind
      where
      showKind :: NameKind -> String
      showKind n = let s = show n in case n of
        Bound                     -> s
        Constructor Inductive     -> "InductiveConstructor"
        Constructor CoInductive   -> "CoinductiveConstructor"
        Datatype                  -> s
        Field                     -> s
        Function                  -> s
        Module                    -> s
        Postulate                 -> s
        Primitive                 -> s
        Record                    -> s
        Argument                  -> s
        Macro                     -> s

-- Escapes special characters.
escape :: Text -> Text
escape (T.uncons -> Nothing)     = T.empty
escape (T.uncons -> Just (c, s)) = T.pack (replace c) <+> escape s
  where
  replace :: Char -> String
  replace c = case c of
    '_'  -> "\\_"
    '{'  -> "\\{"
    '}'  -> "\\}"
    '#'  -> "\\#"
    '$'  -> "\\$"
    '&'  -> "\\&"
    '%'  -> "\\%"
    '~'  -> "\\textasciitilde{}"
    '^'  -> "\\textasciicircum{}"
    '\\' -> "\\textbackslash{}"
    -- Escaping newlines seems to fix the problem caused by pattern
    -- synonyms.
    '\n' -> "\\<\\\\\n\\>"
    _    -> [ c ]
escape _                         = __IMPOSSIBLE__

-- | Fixity declarations need a special treatment. The operations in
-- declarations like:
--
--     infix num op1 op2 op3
--
-- are treated as comments and thus grouped together with the newlines
-- that follow, which results incorrect LaTeX output -- the following
-- state remedies the problem by breaking on newlines.
fixity :: LaTeX ()
fixity = do
  tok <- nextToken

  case T.breakOn (T.pack "\n") tok of

    -- Spaces.
    (sps, nls) | nls == T.empty && isSpaces sps -> do
        spaces $ T.group sps
        fixity

    -- Fixity level.
    (num, nls) | nls == T.empty -> do
        output $ cmdPrefix <+> T.pack "Number" <+> cmdArg num
        fixity

    -- Operations followed by newlines.
    (ops, nls) | otherwise      -> do
        output $ (T.pack " " <+>) $ T.unwords $ map ((cmdPrefix <+> T.pack "FixityOp" <+>) . cmdArg . escape) $ T.words ops
        spaces (T.group nls)


-- | Spaces are grouped before processed, because multiple consecutive
-- spaces determine the alignment of the code and consecutive newline
-- characters need special treatment as well.
spaces :: [Text] -> LaTeX ()
spaces []                                 = return ()
spaces ((T.uncons -> Nothing)       : ss) = __IMPOSSIBLE__

-- Single spaces are ignored.
spaces ((T.uncons -> Just (' ', s)) : []) | T.null s = do
  col <- gets column
  when (col == 0) $ do
    output ptOpen

  moveColumn 1
  output $ T.singleton ' '

-- Multiple spaces.
spaces (s@(T.uncons -> Just (' ', _)) : ss) = do
  let len = T.length s

  col <- gets column
  moveColumn len

  if col /= 0

     then do
       log' Spaces "col /= 0"
       output $ T.singleton ' '
       col <- gets column
       output $ ptClose' col <+> nl <+> ptOpen' col

     else do
       log' Spaces "col == 0"
       indent <- gets indent
       indentPrev <- gets indentPrev

       case compare len indent of

         GT -> do
           log' Spaces "GT"
           setIndent len
           setIndentPrev indent
           output $ ptOpen' indent
           output $ cmdIndent len
           output $ ptClose' len <+> nl <+> ptOpen' len

         EQ -> do
           log' Spaces "EQ"
           output $ ptOpen' indentPrev
           output $ cmdIndent len
           output $ ptClose' len <+> nl <+> ptOpen' len

         LT -> do
           log' Spaces "LT"
           setIndent len
           resetIndentPrev
           output $ ptOpen' 0
           output $ cmdIndent len
           output $ ptClose' len <+> nl <+> ptOpen' len

  spaces ss

-- Newlines.
spaces (s@(T.uncons -> Just ('\n', _)) : ss) = do
  resetColumn
  output $ ptClose <+> T.replicate (T.length s) ptNL
  spaces ss

-- Treat tabs as if they were spaces.
spaces (s@(T.uncons -> Just ('\t', _)) : ss) =
  spaces $ T.replicate (T.length s) (T.singleton ' ') : ss
spaces (_                              : ss) = __IMPOSSIBLE__

------------------------------------------------------------------------
-- * Main.

defaultStyFile :: String
defaultStyFile = "agda.sty"

-- | The only exported function. It's (only) called in @Main.hs@.
generateLaTeX :: TopLevelModuleName -> HighlightingInfo -> TCM ()
generateLaTeX mod hi = do

  options <- TCM.commandLineOptions

  -- There is a default directory given by 'defaultLaTeXDir'.
  let dir = optLaTeXDir options
  liftIO $ createDirectoryIfMissing True dir

  TCM.reportSLn "latex" 1 $ unlines
    [ ""
    , "Checking if " ++ defaultStyFile ++ " is found by the LaTeX environment."
    ]

  merrors <- callCompiler' "kpsewhich" [ "--path=" ++ dir,  defaultStyFile ]

  when (isJust merrors) $ do
    TCM.reportSLn "latex" 1 $ unlines
      [ ""
      , defaultStyFile ++ " was not found. Copying a default version of " ++
          defaultStyFile
      , "into the directory " ++ dir ++ "."
      ]

    liftIO $ do
      styFile <- getDataFileName defaultStyFile
      liftIO $ copyFile styFile (dir </> defaultStyFile)

  let outPath = modToFile mod
  inAbsPath <- filePath <$> (asAbsolutePath =<< Find.findFile mod)

  liftIO $ do
    source <- UTF8.readTextFile inAbsPath
    latex <- E.encodeUtf8 `fmap` toLaTeX source hi
    createDirectoryIfMissing True $ dir </> takeDirectory outPath
    BS.writeFile (dir </> outPath) latex

  where
    modToFile :: TopLevelModuleName -> FilePath
    modToFile m = List.intercalate [pathSeparator] (moduleNameParts m) <.> "tex"

-- | Transforms the source code into LaTeX.
toLaTeX :: String -> HighlightingInfo -> IO Text
toLaTeX source hi

  = processTokens

  -- Head the list (the grouped chars contain the same meta info) and
  -- collect the characters into a string.
  . map (\xs -> case xs of
                    (mi, (pos, _)) : _ ->
                        Token { text     = T.pack $ map (\(_, (_, c)) -> c) xs
                              , info     = fromMaybe mempty mi
                              , position = pos
                              }
                    []                 -> __IMPOSSIBLE__)

  . List.groupBy ((==) `on` fst)  -- Characters which share the same
                                  -- meta info are the same token, so
                                  -- group them together.

  -- Look up the meta info at each position in the highlighting info.
  . map (\(pos, char) ->
        (IntMap.lookup pos infoMap, (pos, char)))

  -- Add position in file to each character.
  . zip [1..]
  $ source
  where
  infoMap = toMap (decompress hi)

processTokens :: Tokens -> IO Text
processTokens ts = do
  (x, _, s) <- runLaTeX nonCode () (emptyState { tokens = ts })
  case x of
    Left "Done" -> return s
    _           -> __IMPOSSIBLE__
