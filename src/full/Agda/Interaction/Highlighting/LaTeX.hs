{-# LANGUAGE BangPatterns #-}
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
import Control.Monad.RWS.Strict
import System.Directory
import System.FilePath
import Data.Text (Text)
import qualified Data.Text               as T
import qualified Data.Text.ICU           as ICU
import qualified Data.Text.IO            as T
import qualified Data.Text.Lazy          as L
import qualified Data.Text.Lazy.Builder  as B
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy    as BS

import qualified Data.IntMap as IntMap
import qualified Data.List   as List

import Paths_Agda

import Agda.Syntax.Abstract (toTopLevelModuleName)
import Agda.Syntax.Common
import Agda.Syntax.Concrete
  (TopLevelModuleName, moduleNameParts, projectRoot)
import qualified Agda.Interaction.FindFile as Find
import Agda.Interaction.Highlighting.Precise
import Agda.TypeChecking.Monad (TCM, Interface(..))
import qualified Agda.TypeChecking.Monad as TCM
import Agda.Interaction.Options (optGHCiInteraction, optLaTeXDir)
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

-- NOTE: This type used to be defined using Text instead of B.Builder.
-- However, this led to seemingly quadratic behaviour, presumably
-- because a Text value was constructed by repeatedly appending things
-- to it.

type LaTeX = ExceptT String (RWST () B.Builder State IO)

-- | Alignment columns.

data AlignmentColumn = AlignmentColumn
  { columnCodeBlock :: !Int
    -- ^ The alignment column's code block.
  , columnColumn    :: !Int
    -- ^ The alignment column.
  } deriving Show

data State = State
  { tokens      :: Tokens
  , codeBlock   :: !Int   -- ^ The number of the current code block.
  , column      :: !Int   -- ^ Column number, used for polytable
                          --   alignment.
  , columns     :: [Int]  -- ^ All alignment columns found on the
                          --   current line (so far), in reverse
                          --   order.
  , columnsPrev :: [AlignmentColumn]
                          -- ^ All alignment columns found in
                          --   previous lines (in any code block),
                          --   with larger columns coming first.
  , inCode      :: !Bool  -- ^ Keeps track of whether we are in a
                          --   code block or not.
  }

type Tokens = [Token]

data Token = Token
  { text     :: !Text
  , info     :: Aspects
  }
  deriving Show

data Debug = MoveColumn | NonCode | Code | Spaces | Output
  deriving (Eq, Show)

-- | Says what debug information should printed.

debugs :: [Debug]
debugs = []

-- | Run function for the @LaTeX@ monad.
runLaTeX ::
  LaTeX a -> () -> State -> IO (Either String a, State, B.Builder)
runLaTeX = runRWST . runExceptT

emptyState :: State
emptyState = State
  { codeBlock   = 0
  , tokens      = []
  , column      = 0
  , columns     = []
  , columnsPrev = []
  , inCode      = False
  }

------------------------------------------------------------------------
-- * Some helpers.

-- | Counts the number of extended grapheme clusters in the string,
-- rather than the number of code points.
--
-- Uses the root locale.

graphemeClusters :: Text -> Int
graphemeClusters = length . ICU.breaks (ICU.breakCharacter ICU.Root)

(<+>) :: Text -> Text -> Text
(<+>) = T.append

isInfixOf' :: Text -> Text -> Maybe (Text, Text)
isInfixOf' needle haystack = go (T.tails haystack) 0
  where
  go []                                         !n = Nothing
  go ((T.stripPrefix needle -> Just suf) : xss)  n = Just (T.take n haystack, suf)
  go (_                                  : xss)  n = go xss (n + 1)

-- Same as above, but starts searching from the back rather than the
-- front.
isInfixOfRev :: Text -> Text -> Maybe (Text, Text)
isInfixOfRev needle haystack
  = case T.reverse needle `isInfixOf'` T.reverse haystack of
      Nothing         -> Nothing
      Just (pre, suf) -> Just (T.reverse suf, T.reverse pre)

isSpaces :: Text -> Bool
isSpaces = T.all (\c -> c == ' ' || c == '\n')

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
            moveColumn $ graphemeClusters $ text t

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
                           Nothing        -> (code, [ suf ])
                           Just (pre', _) ->
                               -- Remove trailing whitespace from the
                               -- final line; the function spaces
                               -- expects trailing whitespace to be
                               -- followed by a newline character.
                             ( T.dropWhileEnd (== ' ') pre'
                             , [ code, suf ]
                             )

              -- This case happens for example when you have two code
              -- blocks after each other, i.e. the begin code of the
              -- second ends up in the suffix of the first's end code.
                    else (pre, [ code, suf ])

          let tokToReturn   = t { text = textToReturn }
          let toksToPutBack = map (\txt -> t { text = txt }) textsToPutBack

          unless (isSpaces textToReturn) $ do
            log MoveColumn textToReturn
            moveColumn $ graphemeClusters textToReturn

          modify $ \s -> s { tokens = toksToPutBack ++ tokens s }
          return tokToReturn

nextToken :: LaTeX Text
nextToken = text `fmap` nextToken'

-- | Merges 'columns' into 'columnsPrev', resets 'column' and
-- 'columns'

resetColumn :: LaTeX ()
resetColumn = modify $ \s ->
  s { column      = 0
    , columnsPrev = merge (codeBlock s) (columns s) (columnsPrev s)
    , columns     = []
    }
  where
  -- Remove shadowed columns from old.
  merge b []  old = old
  merge b new old = new' ++ old'
    where
    new'     = map (\c -> AlignmentColumn
                            { columnCodeBlock = b
                            , columnColumn    = c
                            })
                   new
    old'     = filter ((< leastNew) . columnColumn) old
    leastNew = last new

moveColumn :: Int -> LaTeX ()
moveColumn i = modify $ \s -> s { column = i + column s }

-- | Registers an alignment column.

registerColumn :: LaTeX ()
registerColumn = modify $ \s -> s { columns = column s : columns s }

-- | Registers column zero as an alignment column.

registerColumnZero :: LaTeX ()
registerColumnZero = modify $ \s -> s { columns = [0] }

-- | Changes to the state that are performed at the start of a code
-- block.

-- This code is based on the assumption that there are no
-- non-whitespace characters following \begin{code}. For occurrences
-- of \begin{code} which start a code block this is true. However, the
-- LaTeX backend does not identify code blocks correctly, see Issue
-- #2400.

enterCode :: LaTeX ()
enterCode = do
  resetColumn
  modify $ \s -> s { codeBlock = codeBlock s + 1, inCode = True }

-- | Changes to the state that are performed at the end of a code
-- block.

leaveCode :: LaTeX ()
leaveCode = modify $ \s -> s { inCode = False }

logHelper :: Debug -> Text -> [String] -> LaTeX ()
logHelper debug text extra =
  when (debug `elem` debugs) $ do
    lift $ lift $ T.putStrLn $ T.pack (show debug ++ ": ") <+>
      T.pack "'" <+> text <+> T.pack "' " <+>
      if null extra
         then T.empty
         else T.pack "(" <+> T.pack (unwords extra) <+> T.pack ")"

log :: Debug -> Text -> LaTeX ()
log MoveColumn text = do
  cols <- gets columns
  logHelper MoveColumn text ["columns=", show cols]
log Code text = do
  cols <- gets columns
  col <- gets column
  logHelper Code text ["columns=", show cols, "col=", show col]
log debug text = logHelper debug text []

log' :: Debug -> String -> LaTeX ()
log' d = log d . T.pack

output :: Text -> LaTeX ()
output text = do
  log Output text
  tell (B.fromText text)

------------------------------------------------------------------------
-- * LaTeX and polytable strings.

-- Polytable, http://www.ctan.org/pkg/polytable, is used for code
-- alignment, similar to lhs2TeX's approach.

nl, beginCode, endCode :: Text
nl        = T.pack "%\n"
beginCode = T.pack "\\begin{code}"
endCode   = T.pack "\\end{code}"

ptOpen :: Show a => a -> Text
ptOpen i = T.pack "\\>" <+> T.pack ("[" ++ show i ++ "]")

ptOpenIndent :: Show a => a -> Text -> Text
ptOpenIndent i delta =
  ptOpen i <+> T.pack "[@{}l@{"
           <+> cmdPrefix
           <+> T.pack "Indent"
           <+> cmdArg delta
           <+> T.pack "}]"

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
       enterCode
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

  when (col == 0 && not (isSpaces tok)) $ do
    -- Non-whitespace tokens at the start of a line trigger an
    -- indentation column.
    registerColumnZero
    output $ ptOpen 0

  when (tok == endCode) $ do
    output $ ptClose <+> nl <+> endCode
    leaveCode
    nonCode

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
    Option         -> s
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
    '-'  -> "{-}"
    -- Escaping newlines seems to fix the problem caused by pattern
    -- synonyms.
    '\n' -> "\\<\\\\\n\\>"
    _    -> [ c ]
escape _                         = __IMPOSSIBLE__

-- | Spaces are grouped before processed, because multiple consecutive
-- spaces determine the alignment of the code and consecutive newline
-- characters need special treatment as well.
spaces :: [Text] -> LaTeX ()
spaces [] = return ()

-- Newlines.
spaces (s@(T.uncons -> Just ('\n', _)) : ss) = do
  col <- gets column
  when (col == 0) $
    output $ ptOpen 0
  output $ ptClose <+> T.replicate (graphemeClusters s) ptNL
  resetColumn
  spaces ss

-- Single spaces, or multiple spaces followed by a newline character.
spaces ((T.uncons -> Just (' ', s)) : ss)
  | T.null s || not (null ss) = do

  col <- gets column
  moveColumn (1 + graphemeClusters s)

  when (col == 0) $ do
    -- Single spaces at the start of the line, not followed by more
    -- whitespace, trigger an indentation column and indentation.
    if T.null s && null ss then do
      log' MoveColumn "Register: col = 0, one space"
      registerColumn
      indent 1
    else
      output $ ptOpen 0

  -- For single spaces that are neither at the start nor at the end of
  -- a line a space character is emitted.
  when (col /= 0 && null ss) $
    output $ T.singleton ' '

  spaces ss

-- Multiple spaces, not followed by a newline character.
spaces (s@(T.uncons -> Just (' ', _)) : ss) = do
  let len = graphemeClusters s

  col <- gets column
  moveColumn len
  registerColumn

  if col /= 0

     then do
       log' Spaces "col /= 0"
       output $ T.singleton ' '
       col <- gets column
       output $ ptClose' col <+> nl <+> ptOpen col

     else do
       log' Spaces "col == 0"
       indent len

  spaces ss

spaces _ = __IMPOSSIBLE__

-- | Indents the following code to the given column.

indent :: Int -> LaTeX ()
indent len = do
  columns   <- gets columnsPrev
  codeBlock <- gets codeBlock
  let defaultCol = AlignmentColumn { columnCodeBlock = codeBlock
                                   , columnColumn    = 0
                                   }
      indentFrom = head (filter ((< len) . columnColumn) columns ++
                         [defaultCol])
      blockDelta = codeBlock - columnCodeBlock indentFrom
      delta      = T.pack (show blockDelta)
  log' Spaces (show (indentFrom, len, columns))
  output $ ptOpenIndent (columnColumn indentFrom) delta
  output $ ptClose' len <+> nl <+> ptOpen len

-- Split multi-lines string literals into multiple string literals
-- Isolating leading spaces for the alignment machinery to work
-- properly
stringLiteral :: Token -> Tokens
stringLiteral t | aspect (info t) == Just String =
  reverse $ foldl (\xs x -> t { text = x } : xs) []
          $ concatMap leadingSpaces
          $ List.intersperse (T.pack "\n")
          $ T.lines (text t)
  where
  leadingSpaces :: Text -> [Text]
  leadingSpaces t = [pre, suf]
    where (pre , suf) = T.span (== ' ') t

stringLiteral t = [t]

------------------------------------------------------------------------
-- * Main.

defaultStyFile :: String
defaultStyFile = "agda.sty"

-- | The only exported function.
generateLaTeX :: Interface -> TCM ()
generateLaTeX i = do
  let mod = toTopLevelModuleName $ iModuleName i
      hi  = iHighlighting i

  options <- TCM.commandLineOptions

  dir <- case optGHCiInteraction options of
    False -> return $ optLaTeXDir options
    True  -> do
      sourceFile <- Find.findFile mod
      return $ filePath (projectRoot sourceFile mod)
                 </> optLaTeXDir options
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
  inAbsPath <- liftM filePath (Find.findFile mod)

  liftIO $ do
    source <- UTF8.readTextFile inAbsPath
    latex <- E.encodeUtf8 `fmap` toLaTeX source hi
    createDirectoryIfMissing True $ dir </> takeDirectory outPath
    BS.writeFile (dir </> outPath) latex

  where
    modToFile :: TopLevelModuleName -> FilePath
    modToFile m = List.intercalate [pathSeparator] (moduleNameParts m) <.> "tex"

-- | Transforms the source code into LaTeX.
toLaTeX :: String -> HighlightingInfo -> IO L.Text
toLaTeX source hi

  = processTokens

  . concatMap stringLiteral

  -- Head the list (the grouped chars contain the same meta info) and
  -- collect the characters into a string.
  . map (\xs -> case xs of
                    []          -> __IMPOSSIBLE__
                    (mi, _) : _ ->
                        Token { text = T.pack $ map (\(_, c) -> c) xs
                              , info = fromMaybe mempty mi
                              })

  . List.groupBy ((==) `on` fst)  -- Characters which share the same
                                  -- meta info are the same token, so
                                  -- group them together.

  -- Look up the meta info at each position in the highlighting info.
  . map (\(pos, char) -> (IntMap.lookup pos infoMap, char))

  -- Add position in file to each character.
  . zip [1..]
  . map replaceWhitespace
  $ source
  where
  infoMap = toMap (decompress hi)

  -- Treat everything but new-line characters as spaces [Issue_#2019].
  replaceWhitespace c
    | isSpace c && c /= '\n' = ' '
    | otherwise              = c

processTokens :: Tokens -> IO L.Text
processTokens ts = do
  (x, _, s) <- runLaTeX nonCode () (emptyState { tokens = ts })
  case x of
    Left "Done" -> return (B.toLazyText s)
    _           -> __IMPOSSIBLE__
