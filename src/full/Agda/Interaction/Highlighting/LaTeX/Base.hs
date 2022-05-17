{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}

-- | Function for generating highlighted and aligned LaTeX from literate
-- Agda source.

module Agda.Interaction.Highlighting.LaTeX.Base
  ( generateLaTeXIO
  , prepareCommonAssets
  , runLogLaTeXTWith
  , logMsgToText
  , LogMessage(..)
  , MonadLogLaTeX
  , LogLaTeXT
  , LaTeXOptions(..)
  ) where

import Prelude hiding (log)

import Data.Bifunctor (second)
import Data.Char
import Data.Maybe
import Data.Function
import Data.Foldable (toList)
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif

import Control.Monad (forM_, mapM_, unless, when)
import Control.Monad.Trans.Reader as R ( ReaderT(runReaderT))
import Control.Monad.RWS.Strict
  ( RWST(runRWST)
  , MonadReader(..), asks
  , MonadState(..), gets, modify
  , lift, tell
  )
import Control.Monad.IO.Class
  ( MonadIO(..)
  )

import System.Directory
import System.Exit
import System.FilePath
import System.Process

import Data.Text (Text)
import qualified Data.Text               as T
#ifdef COUNT_CLUSTERS
import qualified Data.Text.ICU           as ICU
#endif
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
import Agda.Syntax.Concrete (TopLevelModuleName, moduleNameParts)
import Agda.Syntax.Parser.Literate (literateTeX, LayerRole, atomizeLayers)
import qualified Agda.Syntax.Parser.Literate as L
import Agda.Syntax.Position (startPos)

import Agda.Interaction.Highlighting.Precise hiding (toList)

import Agda.TypeChecking.Monad (Interface(..))

import Agda.Utils.FileName (AbsolutePath)
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Functor  ((<&>))
import Agda.Utils.List     (last1, updateHead, updateLast)
import Agda.Utils.Maybe    (whenJust)
import qualified Agda.Utils.List1 as List1

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Logging

class Monad m => MonadLogLaTeX m where
  logLaTeX :: LogMessage -> m ()

-- | Log LaTeX messages using a provided action.
--
-- This could be accomplished by putting logs into the RWST output and splitting it
-- into a WriterT, but that becomes slightly more complicated to reason about in
-- the presence of IO exceptions.
--
-- We want the logging to be reasonably polymorphic, avoid space leaks that can occur
-- with WriterT, and also be usable during outer phases such as directory preparation.
--
-- I'm not certain this is the best way to do it, but whatever.
type LogLaTeXT m = ReaderT (LogMessage -> m ()) m

instance Monad m => MonadLogLaTeX (LogLaTeXT m) where
  logLaTeX message = do
    doLog <- ask
    lift $ doLog message

runLogLaTeXTWith :: Monad m => (LogMessage -> m ()) -> LogLaTeXT m a -> m a
runLogLaTeXTWith = flip runReaderT

-- Not currently used, but for example:
-- runLogLaTeXWithIO :: MonadIO m => LogLaTeXT m a -> m a
-- runLogLaTeXWithIO = runLogLaTeXTWith $ liftIO . T.putStrLn . logMsgToText

------------------------------------------------------------------------
-- * Datatypes.

-- | The @LaTeX@ monad is a combination of @ExceptT@, @RWST@ and
-- a logger @m@. The error part is just used to keep track whether we finished or
-- not, the reader part contains static options used, the writer is where the
-- output goes and the state is for keeping track of the tokens and some
-- other useful info, and the MonadLogLaTeX part is used for printing debugging info.

type LaTeX a = forall m. MonadLogLaTeX m => RWST Env [Output] State m a

-- | Output items.

data LogMessage = LogMessage Debug Text [Text] deriving Show

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

-- | Type of function for estimating column width of text.

type TextWidthEstimator = Text -> Int

data Env = Env
  { estimateTextWidth :: !TextWidthEstimator
    -- ^ How to estimate the column width of text (i.e. Count extended grapheme clusters vs. code points).
  , debugs :: [Debug]
    -- ^ Says what debug information should printed.
  }

data State = State
  { codeBlock     :: !Int   -- ^ The number of the current code block.
  , column        :: !Int   -- ^ The current column number.
  , columns       :: [AlignmentColumn]
                            -- ^ All alignment columns found on the
                            --   current line (so far), in reverse
                            --   order.
  , columnsPrev   :: [AlignmentColumn]
                            -- ^ All alignment columns found in
                            --   previous lines (in any code block),
                            --   with larger columns coming first.
  , nextId        :: !IndentationColumnId
                            -- ^ The next indentation column
                            -- identifier.
  , usedColumns   :: HashSet IndentationColumnId
                            -- ^ Indentation columns that have
                            -- actually
                            --   been used.
  }

type Tokens = [Token]

data Token = Token
  { text     :: !Text
  , info     :: Aspects
  }
  deriving Show

withTokenText :: (Text -> Text) -> Token -> Token
withTokenText f tok@Token{text = t} = tok{text = f t}

data Debug = MoveColumn | NonCode | Code | Spaces | Output | FileSystem
  deriving (Eq, Show)

-- | Run function for the @LaTeX@ monad.
runLaTeX :: MonadLogLaTeX m =>
  LaTeX a -> Env -> State -> m (a, State, [Output])
-- ASR (2021-02-07). The eta-expansion is required by GHC >= 9.0.1
-- (see Issue #4955).
runLaTeX l = runRWST l

emptyState :: State
emptyState = State
  { codeBlock     = 0
  , column        = 0
  , columns       = []
  , columnsPrev   = []
  , nextId        = 0
  , usedColumns   = Set.empty
  }

emptyEnv
  :: TextWidthEstimator  -- ^ Count extended grapheme clusters?
  -> Env
emptyEnv twe = Env twe []


------------------------------------------------------------------------
-- * Some helpers.

-- | Gives the size of the string. If cluster counting is enabled,
-- then the number of extended grapheme clusters is computed (the root
-- locale is used), and otherwise the number of code points.

size :: Text -> LaTeX Int
size t = asks estimateTextWidth <&> ($ t)

-- | Does the string consist solely of whitespace?

isSpaces :: Text -> Bool
isSpaces = T.all isSpace

-- | Is the character a whitespace character distinct from '\n'?

isSpaceNotNewline :: Char -> Bool
isSpaceNotNewline c = isSpace c && c /= '\n'

-- | Replaces all forms of whitespace, except for new-line characters,
-- with spaces.

replaceSpaces :: Text -> Text
replaceSpaces = T.map (\c -> if isSpaceNotNewline c then ' ' else c)


-- | If the `Token` consists of spaces, the internal column counter is advanced
--   by the length of the token. Otherwise, `moveColumnForToken` is a no-op.
moveColumnForToken :: Token -> LaTeX ()
moveColumnForToken Token{ text = t } = do
  unless (isSpaces t) $ do
    log MoveColumn t
    -- ASR (2021-02-07). The eta-expansion is required by GHC >= 9.0.1
    -- (see Issue #4955).
    n <- size t
    moveColumn n

-- | Merges 'columns' into 'columnsPrev', resets 'column' and
-- 'columns'

resetColumn :: LaTeX ()
resetColumn = modify $ \s ->
  s { column      = 0
    , columnsPrev = mergeCols (columns s) (columnsPrev s)
    , columns     = []
    }
  where
  -- Remove shadowed columns from old.
  mergeCols []         old = old
  mergeCols new@(n:ns) old = new ++ filter ((< leastNew) . columnColumn) old
    where
    leastNew = columnColumn (last1 n ns)

moveColumn :: Int -> LaTeX ()
moveColumn i = modify $ \s -> s { column = i + column s }

-- | Registers a column of the given kind. The column is returned.

registerColumn :: Kind -> LaTeX AlignmentColumn
registerColumn kind = do
  column    <- gets column
  codeBlock <- gets codeBlock
  colKind   <- case kind of
                 Alignment   -> return Nothing
                 Indentation -> do
                   nextId <- gets nextId
                   modify $ \s -> s { nextId = succ nextId }
                   return (Just nextId)
  let c = AlignmentColumn { columnColumn    = column
                          , columnCodeBlock = codeBlock
                          , columnKind      = colKind
                          }
  modify $ \s -> s { columns = c : columns s }
  return c

-- | Registers the given column as used (if it is an indentation
-- column).

useColumn :: AlignmentColumn -> LaTeX ()
useColumn c = whenJust (columnKind c) $ \ i ->
  modify $ \ s -> s { usedColumns = Set.insert i (usedColumns s) }

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

enterCode :: LaTeX ()
enterCode = do
  resetColumn
  modify $ \s -> s { codeBlock = codeBlock s + 1 }

-- | Changes to the state that are performed at the end of a code
-- block.

leaveCode :: LaTeX ()
leaveCode = return ()

tshow :: Show a => a -> Text
tshow = T.pack . show

logMsgToText :: LogMessage -> Text
logMsgToText (LogMessage messageLabel text extra) = T.concat $
  [ tshow messageLabel, ": '", text, "' "
  ] ++ if null extra then [] else ["(", T.unwords extra, ")"]

logHelper :: Debug -> Text -> [Text] -> LaTeX ()
logHelper debug text extra = do
  logLevels <- debugs <$> ask
  when (debug `elem` logLevels) $ do
    lift $ logLaTeX (LogMessage debug text extra)

log :: Debug -> Text -> LaTeX ()
log MoveColumn text = do
  cols <- gets columns
  logHelper MoveColumn text ["columns=", tshow cols]
log Code text = do
  cols <- gets columns
  col <- gets column
  logHelper Code text ["columns=", tshow cols, "col=", tshow col]
log debug text = logHelper debug text []

output :: Output -> LaTeX ()
output item = do
  log Output $ tshow item
  tell [item]

------------------------------------------------------------------------
-- * LaTeX and polytable strings.

-- Polytable, http://www.ctan.org/pkg/polytable, is used for code
-- alignment, similar to lhs2TeX's approach.

nl :: Text
nl = "%\n"

-- | A command that is used when two tokens are put next to each other
-- in the same column.

agdaSpace :: Text
agdaSpace = cmdPrefix <> "Space" <> cmdArg T.empty <> nl

-- | The column's name.
--
-- Indentation columns have unique names, distinct from all alignment
-- column names.

columnName :: AlignmentColumn -> Text
columnName c = T.pack $ case columnKind c of
  Nothing -> show (columnColumn c)
  Just i  -> show i ++ "I"

-- | Opens a column with the given name.

ptOpen' :: Text -> Text
ptOpen' name = "\\>[" <> name <> "]"

-- | Opens the given column.

ptOpen :: AlignmentColumn -> Text
ptOpen c = ptOpen' (columnName c)

-- | Opens a special column that is only used at the beginning of
-- lines.

ptOpenBeginningOfLine :: Text
ptOpenBeginningOfLine = ptOpen' "." <> "[@{}l@{}]"

-- | Opens the given column, and inserts an indentation instruction
-- with the given argument at the end of it.

ptOpenIndent
  :: AlignmentColumn
  -> Int              -- ^ Indentation instruction argument.
  -> Text
ptOpenIndent c delta =
  ptOpen c <> "[@{}l@{"
           <> cmdPrefix
           <> "Indent"
           <> cmdArg (T.pack $ show delta)
           <> "}]"

ptClose :: Text
ptClose = "\\<"

ptClose' :: AlignmentColumn -> Text
ptClose' c =
  ptClose <> "[" <> columnName c <> "]"

ptNL :: Text
ptNL = nl <> "\\\\\n"

ptEmptyLine :: Text
ptEmptyLine =
  nl <> "\\\\["
     <> cmdPrefix
     <> "EmptyExtraSkip"
     <> "]%\n"

cmdPrefix :: Text
cmdPrefix = "\\Agda"

cmdArg :: Text -> Text
cmdArg x = "{" <> x <> "}"

------------------------------------------------------------------------
-- * Output generation from a stream of labelled tokens.

processLayers :: [(LayerRole, Tokens)] -> LaTeX ()
-- ASR (2021-02-07). The eta-expansion on @lt@ is required by GHC >=
-- 9.0.1 (see Issue #4955).
processLayers lt = forM_ lt $ \ (layerRole,toks) -> do
  case layerRole of
    L.Markup  -> processMarkup  toks
    L.Comment -> processComment toks
    L.Code    -> processCode    toks

-- | Deals with markup, which is output verbatim.
processMarkup :: Tokens -> LaTeX ()
-- ASR (2021-02-07). The eta-expansion on @ts@ is required by GHC >=
-- 9.0.1 (see Issue #4955).
processMarkup ts = forM_ ts $ \ t' -> do
  moveColumnForToken t'
  output (Text (text t'))

-- | Deals with literate text, which is output verbatim
processComment :: Tokens -> LaTeX ()
-- ASR (2021-02-07). The eta-expansion with @ts@ is required by GHC >=
-- 9.0.1 (see Issue #4955).
processComment ts = forM_ ts $ \ t' -> do
  unless ("%" == T.take 1 (T.stripStart (text t'))) $ do
    moveColumnForToken t'
  output (Text (text t'))

-- | Deals with code blocks. Every token, except spaces, is pretty
-- printed as a LaTeX command.
processCode :: Tokens -> LaTeX ()
processCode toks' = do
  output $ Text nl
  enterCode
  mapM_ go toks'
  ptOpenWhenColumnZero =<< gets column
  output $ Text $ ptClose <> nl
  leaveCode

  where
    go tok'@Token{ text = tok } = do
      -- Get the column information before grabbing the token, since
      -- grabbing (possibly) moves the column.
      col  <- gets column

      moveColumnForToken tok'
      log Code tok

      unless (T.null tok) $
        if (isSpaces tok) then do
            spaces $ T.group $ replaceSpaces tok
        else do
          ptOpenWhenColumnZero col
          output $ Text $
            -- we return the escaped token wrapped in commands corresponding
            -- to its aspect (if any) and other aspects (e.g. error, unsolved meta)
            foldr (\c t -> cmdPrefix <> T.pack c <> cmdArg t)
                  (escape tok)
                  $ map fromOtherAspect (toList $ otherAspects $ info tok') ++
                    concatMap fromAspect (toList $ aspect $ info tok')

    -- Non-whitespace tokens at the start of a line trigger an
    -- alignment column.
    ptOpenWhenColumnZero col =
        when (col == 0) $ do
          registerColumnZero
          -- ASR (2021-02-07). The eta-expansion @\o -> output o@ is
          -- required by GHC >= 9.0.1 (see Issue #4955).
          (\o -> output o). Text . ptOpen =<< columnZero

    -- Translation from OtherAspect to command strings. So far it happens
    -- to correspond to @show@ but it does not have to (cf. fromAspect)
    fromOtherAspect :: OtherAspect -> String
    fromOtherAspect = show

    fromAspect :: Aspect -> [String]
    fromAspect a = let s = [show a] in case a of
      Comment           -> s
      Keyword           -> s
      Hole              -> s
      String            -> s
      Number            -> s
      Symbol            -> s
      PrimitiveType     -> s
      Pragma            -> s
      Background        -> s
      Markup            -> s
      Name Nothing isOp -> fromAspect (Name (Just Postulate) isOp)
        -- At the time of writing the case above can be encountered in
        -- --only-scope-checking mode, for instance for the token "Size"
        -- in the following code:
        --
        --   {-# BUILTIN SIZE Size #-}
        --
        -- The choice of "Postulate" works for this example, but might
        -- be less appropriate for others.
      Name (Just kind) isOp ->
        (\c -> if isOp then ["Operator", c] else [c]) $
        case kind of
          Bound                     -> sk
          Generalizable             -> sk
          Constructor Inductive     -> "InductiveConstructor"
          Constructor CoInductive   -> "CoinductiveConstructor"
          Datatype                  -> sk
          Field                     -> sk
          Function                  -> sk
          Module                    -> sk
          Postulate                 -> sk
          Primitive                 -> sk
          Record                    -> sk
          Argument                  -> sk
          Macro                     -> sk
        where
        sk = show kind

-- | Escapes special characters.
escape :: Text -> Text
escape (T.uncons -> Nothing)     = T.empty
escape (T.uncons -> Just (c, s)) = T.pack (replace c) <> escape s
  where
  replace :: Char -> String
  replace char = case char of
    '_'  -> "\\AgdaUnderscore{}"
    '{'  -> "\\{"
    '}'  -> "\\}"
    '#'  -> "\\#"
    '$'  -> "\\$"
    '&'  -> "\\&"
    '%'  -> "\\%"
    '~'  -> "\\textasciitilde{}"
    '^'  -> "\\textasciicircum{}"
    '\\' -> "\\textbackslash{}"
    ' '  -> "\\ "
    _    -> [ char ]
#if __GLASGOW_HASKELL__ < 810
escape _                         = __IMPOSSIBLE__
#endif

-- | Every element in the list should consist of either one or more
-- newline characters, or one or more space characters. Two adjacent
-- list elements must not contain the same character.
--
-- If the final element of the list consists of spaces, then these
-- spaces are assumed to not be trailing whitespace.
spaces :: [Text] -> LaTeX ()
spaces [] = return ()

-- Newlines.
spaces (s@(T.uncons -> Just ('\n', _)) : ss) = do
  col <- gets column
  when (col == 0) $
    -- ASR (2021-02-07). The eta-expansion @\o -> output o@ is
    -- required by GHC >= 9.0.1 (see Issue #4955).
    (\o -> output o) . Text . ptOpen =<< columnZero
  output $ Text $ ptClose <> ptNL <>
                  T.replicate (T.length s - 1) ptEmptyLine
  resetColumn
  spaces ss

-- Spaces followed by a newline character.
spaces (_ : ss@(_ : _)) = spaces ss

-- Spaces that are not followed by a newline character.
spaces [ s ] = do
  col <- gets column

  let len  = T.length s
      kind = if col /= 0 && len == 1
             then Indentation
             else Alignment

  moveColumn len
  column <- registerColumn kind

  if col /= 0
  then log Spaces "col /= 0"
  else do
    columns    <- gets columnsPrev
    codeBlock  <- gets codeBlock

    log Spaces $
      "col == 0: " <> T.pack (show (len, columns))

    case filter ((<= len) . columnColumn) columns of
      c : _ | columnColumn c == len, isJust (columnKind c) -> do
        -- Align. (This happens automatically if the column is an
        -- alignment column, but c is an indentation column.)
        useColumn c
        output $ Text $ ptOpenBeginningOfLine
        output $ Text $ ptClose' c
      c : _ | columnColumn c <  len -> do
        -- Indent.
        useColumn c
        output $ Text $ ptOpenIndent c (codeBlock - columnCodeBlock c)
      _ -> return ()

  output $ MaybeColumn column

-- | Split multi-lines string literals into multiple string literals
-- Isolating leading spaces for the alignment machinery to work
-- properly
stringLiteral :: Token -> Tokens
stringLiteral t | aspect (info t) == Just String =
  map (\ x -> t { text = x })
          $ concatMap leadingSpaces
          $ List.intersperse "\n"
          $ T.lines (text t)
  where
  leadingSpaces :: Text -> [Text]
  leadingSpaces tok = [pre, suf]
    where (pre , suf) = T.span isSpaceNotNewline tok

stringLiteral t = [t]

-- | Split multi-line comments into several tokens.
-- See issue #5398.
multiLineComment :: Token -> Tokens
multiLineComment Token{ text = s, info = i } | aspect i == Just Comment =
  map (`Token` i)
    $ List.intersperse "\n"
    $ T.lines s
-- multiLineComment Token{ text = s, info = i } | aspect i == Just Comment =
--   map emptyToPar
--     $ List1.groupBy ((==) `on` T.null)
--     $ T.lines s
--   where
--   emptyToPar :: List1 Text -> Token
--   emptyToPar ts@(t :| _)
--     | T.null t  = Token{ text = "\n", info = mempty }
--     | otherwise = Token{ text = sconcat $ List1.intersperse "\n" ts, info = i }
multiLineComment t = [t]

------------------------------------------------------------------------
-- * Main.

-- | The Agda data directory containing the files for the LaTeX backend.

latexDataDir :: FilePath
latexDataDir = "latex"

defaultStyFile :: String
defaultStyFile = "agda.sty"

data LaTeXOptions = LaTeXOptions
  { latexOptOutDir         :: FilePath
  , latexOptSourceFileName :: Maybe AbsolutePath
    -- ^ The parser uses a @Position@ which includes a source filename for
    -- error reporting and such. We don't actually get the source filename
    -- with an @Interface@, and it isn't necessary to look it up.
    -- This is a "nice-to-have" parameter.
  , latexOptCountClusters  :: Bool
    -- ^ Count extended grapheme clusters rather than code points when
    -- generating LaTeX.
  }

getTextWidthEstimator :: Bool -> TextWidthEstimator
getTextWidthEstimator _countClusters =
#ifdef COUNT_CLUSTERS
  if _countClusters
    then length . (ICU.breaks (ICU.breakCharacter ICU.Root))
    else T.length
#else
  T.length
#endif

-- | Create the common base output directory and check for/install the style file.
prepareCommonAssets :: (MonadLogLaTeX m, MonadIO m) => FilePath -> m ()
prepareCommonAssets dir = do
  liftIO $ createDirectoryIfMissing True dir
  (code, _, _) <-
    liftIO $
      readProcessWithExitCode
        "kpsewhich"
        ["--path=" ++ dir, defaultStyFile]
        ""
  when (code /= ExitSuccess) $ do
    logLaTeX $ LogMessage FileSystem
      (T.pack $ unwords [defaultStyFile, "was not found. Copying a default version of", defaultStyFile, "into", dir])
      []
    liftIO $ do
      styFile <- getDataFileName $
        latexDataDir </> defaultStyFile
      copyFile styFile (dir </> defaultStyFile)

-- | Generates a LaTeX file for the given interface.
generateLaTeXIO :: (MonadLogLaTeX m, MonadIO m) => LaTeXOptions -> Interface -> m ()
generateLaTeXIO opts i = do
  let textWidthEstimator = getTextWidthEstimator (latexOptCountClusters opts)
  let baseDir = latexOptOutDir opts
  let outPath = baseDir </> (latexOutRelativeFilePath $ toTopLevelModuleName $ iModuleName i)
  latex <- E.encodeUtf8 <$> toLaTeX
              (emptyEnv textWidthEstimator)
              (latexOptSourceFileName opts)
              (iSource i)
              (iHighlighting i)
  liftIO $ do
    createDirectoryIfMissing True (takeDirectory outPath)
    BS.writeFile outPath latex

latexOutRelativeFilePath :: TopLevelModuleName -> FilePath
latexOutRelativeFilePath m = List.intercalate [pathSeparator] (List1.toList $ moduleNameParts m) <.> "tex"

groupByFst :: forall a b. Eq a => [(a,b)] -> [(a,[b])]
groupByFst =
    map (\xs -> case xs of                     -- Float the grouping to the top level
          []           -> __IMPOSSIBLE__
          (tag, _): _ -> (tag, map snd xs))

  . List.groupBy ((==) `on` fst)  -- Group together characters in the same
                                  -- role.

-- | Transforms the source code into LaTeX.
toLaTeX
  :: MonadLogLaTeX m
  => Env
  -> Maybe AbsolutePath
  -> L.Text
  -> HighlightingInfo
  -> m L.Text
toLaTeX env path source hi =

  processTokens env

    . map
      ( ( \(role, tokens) ->
            (role,) $
              -- This bit fixes issue 954
              ( applyWhen (L.isCode role) $
                  -- Remove trailing whitespace from the
                  -- final line; the function spaces
                  -- expects trailing whitespace to be
                  -- followed by a newline character.
                    whenMoreThanOne
                      ( updateLast
                          $ withTokenText
                          $ \suf ->
                            maybe
                              suf
                              (T.dropWhileEnd isSpaceNotNewline)
                              (T.stripSuffix "\n" suf)
                      )
                      . updateLast (withTokenText $ T.dropWhileEnd isSpaceNotNewline)
                      . updateHead
                        ( withTokenText $
                            \pre ->
                              fromMaybe pre $ T.stripPrefix "\n" $
                                T.dropWhile
                                  isSpaceNotNewline
                                  pre
                        )
              )
                tokens
        ) . ( second
                ( -- Split tokens at newlines
                  concatMap stringLiteral
                . concatMap multiLineComment
                . map ( \(mi, cs) ->
                              Token {text = T.pack cs, info = fromMaybe mempty mi}
                      )
                . groupByFst
                )
            )
      )
    . groupByFst

  -- Look up the meta info at each position in the highlighting info.
  . zipWith (\pos (role, char) -> (role, (IntMap.lookup pos infoMap, char)))
            [1..] . -- Add position in file to each character.
              -- Map each character to its role
              atomizeLayers . literateTeX (startPos path)

  $ L.unpack source
  where
  infoMap = toMap hi

  whenMoreThanOne :: ([a] -> [a]) -> [a] -> [a]
  whenMoreThanOne f xs@(_:_:_) = f xs
  whenMoreThanOne _ xs         = xs


processTokens
  :: MonadLogLaTeX m
  => Env
  -> [(LayerRole, Tokens)]
  -> m L.Text
processTokens env ts = do
  ((), s, os) <- runLaTeX (processLayers ts) env emptyState
  return $ L.fromChunks $ map (render s) os
  where
    render _ (Text s)        = s
    render s (MaybeColumn c)
      | Just i <- columnKind c,
        not (i `Set.member` usedColumns s) = agdaSpace
      | otherwise                          = nl <> ptOpen c
