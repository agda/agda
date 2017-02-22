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
import qualified Data.Text.Lazy.Encoding as E
import qualified Data.ByteString.Lazy    as BS

import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.IntMap  as IntMap
import qualified Data.List    as List

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

type LaTeX = ExceptT String (RWST () [Output] State IO)

-- | Output items.

data Output
  = Text !Text
    -- ^ A piece of text.
  | MaybeColumn !AlignmentColumn
    -- ^ A column. If it turns out to be an indentation column that is
    --   not used to indent or align something, then no column will be
    --   generated, only whitespace ('agdaSpace').
  deriving Show

-- | Column kinds.

data Kind
  = Indentation
    -- ^ Used only for indentation (the placement of the first token
    -- on a line, relative to tokens on previous lines).
  | Alignment
    -- ^ Used both for indentation and for alignment.
  deriving (Eq, Show)

-- | Unique identifiers for indentation columns.

type IndentationColumnId = Int

-- | Alignment and indentation columns.

data AlignmentColumn = AlignmentColumn
  { columnCodeBlock :: !Int
    -- ^ The column's code block.
  , columnColumn :: !Int
    -- ^ The column number.
  , columnKind :: Maybe IndentationColumnId
    -- ^ The column kind. 'Nothing' for alignment columns and @'Just'
    -- i@ for indentation columns, where @i@ is the column's unique
    -- identifier.
  } deriving Show

data State = State
  { tokens      :: Tokens
  , codeBlock   :: !Int   -- ^ The number of the current code block.
  , column      :: !Int   -- ^ The current column number.
  , columns     :: [AlignmentColumn]
                          -- ^ All alignment columns found on the
                          --   current line (so far), in reverse
                          --   order.
  , columnsPrev :: [AlignmentColumn]
                          -- ^ All alignment columns found in
                          --   previous lines (in any code block),
                          --   with larger columns coming first.
  , inCode      :: !Bool  -- ^ Keeps track of whether we are in a
                          --   code block or not.
  , nextId      :: !IndentationColumnId
                          -- ^ The next indentation column identifier.
  , usedColumns :: HashSet IndentationColumnId
                          -- ^ Indentation columns that have actually
                          --   been used.
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
  LaTeX a -> () -> State -> IO (Either String a, State, [Output])
runLaTeX = runRWST . runExceptT

emptyState :: State
emptyState = State
  { codeBlock   = 0
  , tokens      = []
  , column      = 0
  , columns     = []
  , columnsPrev = []
  , inCode      = False
  , nextId      = 0
  , usedColumns = Set.empty
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
    , columnsPrev = merge (columns s) (columnsPrev s)
    , columns     = []
    }
  where
  -- Remove shadowed columns from old.
  merge []  old = old
  merge new old = new ++ filter ((< leastNew) . columnColumn) old
    where
    leastNew = columnColumn (last new)

moveColumn :: Int -> LaTeX ()
moveColumn i = modify $ \s -> s { column = i + column s }

-- | Registers a column of the given kind. The column is returned.

registerColumn :: Kind -> LaTeX AlignmentColumn
registerColumn kind = do
  column    <- gets column
  codeBlock <- gets codeBlock
  kind      <- case kind of
                 Alignment   -> return Nothing
                 Indentation -> do
                   nextId <- gets nextId
                   modify $ \s -> s { nextId = succ nextId }
                   return (Just nextId)
  let c = AlignmentColumn { columnColumn    = column
                          , columnCodeBlock = codeBlock
                          , columnKind      = kind
                          }
  modify $ \s -> s { columns = c : columns s }
  return c

-- | Registers the given column as used (if it is an indentation
-- column).

useColumn :: AlignmentColumn -> LaTeX ()
useColumn c = case columnKind c of
  Nothing -> return ()
  Just i  -> modify $ \s ->
               s { usedColumns = Set.insert i (usedColumns s) }

-- | Alignment column zero in the current code block.

columnZero :: LaTeX AlignmentColumn
columnZero = do
  codeBlock <- gets codeBlock
  return $ AlignmentColumn { columnColumn    = 0
                           , columnCodeBlock = codeBlock
                           , columnKind      = Nothing
                           }

-- | Registers column zero as an alignment column.

registerColumnZero :: LaTeX ()
registerColumnZero = do
  c <- columnZero
  modify $ \s -> s { columns = [c] }

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

output :: Output -> LaTeX ()
output item = do
  log' Output (show item)
  tell [item]

------------------------------------------------------------------------
-- * LaTeX and polytable strings.

-- Polytable, http://www.ctan.org/pkg/polytable, is used for code
-- alignment, similar to lhs2TeX's approach.

nl, beginCode, endCode :: Text
nl        = T.pack "%\n"
beginCode = T.pack "\\begin{code}"
endCode   = T.pack "\\end{code}"

-- | A command that is used when two tokens are put next to each other
-- in the same column.

agdaSpace :: Text
agdaSpace = cmdPrefix <+> T.pack "Space" <+> cmdArg T.empty <+> nl

-- | The column's name.
--
-- Indentation columns have unique names, distinct from all alignment
-- column names.

columnName :: AlignmentColumn -> Text
columnName c = T.pack $ case columnKind c of
  Nothing -> show (columnColumn c)
  Just i  -> show i ++ "I"

ptOpen :: AlignmentColumn -> Text
ptOpen c = T.pack "\\>[" <+> columnName c <+> T.singleton ']'

ptOpenIndent :: AlignmentColumn -> Int -> Text
ptOpenIndent c delta =
  ptOpen c <+> T.pack "[@{}l@{"
           <+> cmdPrefix
           <+> T.pack "Indent"
           <+> cmdArg (T.pack $ show delta)
           <+> T.pack "}]"

ptClose :: Text
ptClose = T.pack "\\<"

ptClose' :: AlignmentColumn -> Text
ptClose' c =
  ptClose <+> T.singleton '[' <+> columnName c <+> T.singleton ']'

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
       output $ Text $ beginCode <+> nl
       enterCode
       code

     else do
       output $ Text tok
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
    -- alignment column.
    registerColumnZero
    output . Text . ptOpen =<< columnZero

  when (tok == endCode) $ do
    output $ Text $ ptClose <+> nl <+> endCode
    leaveCode
    nonCode

  when (isSpaces tok) $ do
    spaces $ T.group tok
    code

  case aspect (info tok') of
    Nothing -> output $ Text $ escape tok
    Just a  -> output $ Text $
                 cmdPrefix <+> T.pack (cmd a) <+> cmdArg (escape tok)

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
--
-- If the final element of the list consists of spaces, then these
-- spaces are assumed to not be trailing whitespace.
spaces :: [Text] -> LaTeX ()
spaces [] = return ()

-- Newlines.
spaces (s@(T.uncons -> Just ('\n', _)) : ss) = do
  col <- gets column
  when (col == 0) $
    output . Text . ptOpen =<< columnZero
  output $ Text $ ptClose <+> T.replicate (graphemeClusters s) ptNL
  resetColumn
  spaces ss

-- Spaces followed by a newline character.
spaces (_ : ss@(_ : _)) = spaces ss

-- Spaces that are not followed by a newline character.
spaces [ s ] = do
  col <- gets column

  let len  = graphemeClusters s
      kind = if col /= 0 && len == 1
             then Indentation
             else Alignment

  moveColumn len
  column <- registerColumn kind

  if col /= 0
  then log' Spaces "col /= 0"
  else do
    columns    <- gets columnsPrev
    codeBlock  <- gets codeBlock
    defaultCol <- columnZero

    let (alignWith, indentFrom) =
          case filter ((<= len) . columnColumn) columns ++
               [defaultCol] of
            c1 : c2 : _ | columnColumn c1 == len -> (Just c1, c2)
            c : _       | columnColumn c  <  len -> (Nothing, c)
            _                                    -> __IMPOSSIBLE__

    log' Spaces $
      "col == 0: " ++ show (alignWith, indentFrom, len, columns)

    -- Indent.
    useColumn indentFrom
    output $ Text $
      ptOpenIndent indentFrom (codeBlock - columnCodeBlock indentFrom)

    -- Align (in some cases).
    case alignWith of
      Just (alignWith@AlignmentColumn { columnKind = Just _ }) -> do
          useColumn alignWith
          output $ Text $ ptClose' alignWith
      _ -> return ()

  output $ MaybeColumn column

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
  (x, s, os) <- runLaTeX nonCode () (emptyState { tokens = ts })
  case x of
    Left "Done" -> return $ L.fromChunks $ map (render s) os
    _           -> __IMPOSSIBLE__
  where
  render _ (Text s)        = s
  render s (MaybeColumn c)
    | Just i <- columnKind c,
      not (Set.member i (usedColumns s)) = agdaSpace
    | otherwise                          = nl <+> ptOpen c
