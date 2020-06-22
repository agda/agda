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
import Data.Foldable (toList)
import Control.Monad.RWS.Strict
import Control.Arrow (second)
import System.Directory
import System.Exit
import System.FilePath
import System.Process
import Data.Text (Text)
import qualified Data.Text               as T
#ifdef COUNT_CLUSTERS
import qualified Data.Text.ICU           as ICU
#endif
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
import Agda.Syntax.Parser.Literate (literateTeX, LayerRole, atomizeLayers)
import qualified Agda.Syntax.Parser.Literate as L
import Agda.Syntax.Position (startPos)

import qualified Agda.Interaction.FindFile as Find
import Agda.Interaction.Highlighting.Precise
import qualified Agda.Interaction.Options as O

import Agda.TypeChecking.Monad (TCM, Interface(..))
import qualified Agda.TypeChecking.Monad as TCM

import Agda.Utils.FileName (filePath, AbsolutePath, mkAbsolute)
import qualified Agda.Utils.List1 as List1

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Datatypes.

-- | The @LaTeX@ monad is a combination of @ExceptT@, @RWST@ and
-- @IO@. The error part is just used to keep track whether we finished
-- or not, the reader part isn't used, the writer is where the output
-- goes and the state is for keeping track of the tokens and some other
-- useful info, and the I/O part is used for printing debugging info.

type LaTeX = RWST () [Output] State IO

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
  , countClusters :: !Bool  -- ^ Count extended grapheme clusters?
  }

type Tokens = [Token]

data Token = Token
  { text     :: !Text
  , info     :: Aspects
  }
  deriving Show

withTokenText :: (Text -> Text) -> Token -> Token
withTokenText f tok@Token{text = t} = tok{text = f t}

data Debug = MoveColumn | NonCode | Code | Spaces | Output
  deriving (Eq, Show)

-- | Says what debug information should printed.

debugs :: [Debug]
debugs = []

-- | Run function for the @LaTeX@ monad.
runLaTeX ::
  LaTeX a -> () -> State -> IO (a, State, [Output])
runLaTeX = runRWST

emptyState
  :: Bool  -- ^ Count extended grapheme clusters?
  -> State
emptyState cc = State
  { codeBlock     = 0
  , column        = 0
  , columns       = []
  , columnsPrev   = []
  , nextId        = 0
  , usedColumns   = Set.empty
  , countClusters = cc
  }

------------------------------------------------------------------------
-- * Some helpers.

-- | Gives the size of the string. If cluster counting is enabled,
-- then the number of extended grapheme clusters is computed (the root
-- locale is used), and otherwise the number of code points.

size :: Text -> LaTeX Int
size t = do
  cc <- countClusters <$> get
  if cc then
#ifdef COUNT_CLUSTERS
    return $ length $ ICU.breaks (ICU.breakCharacter ICU.Root) t
#else
    __IMPOSSIBLE__
#endif
   else
    return $ T.length t

(<+>) :: Text -> Text -> Text
(<+>) = T.append

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
moveColumnForToken t = do
  unless (isSpaces (text t)) $ do
    log MoveColumn $ text t
    moveColumn =<< size (text t)

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

enterCode :: LaTeX ()
enterCode = do
  resetColumn
  modify $ \s -> s { codeBlock = codeBlock s + 1 }

-- | Changes to the state that are performed at the end of a code
-- block.

leaveCode :: LaTeX ()
leaveCode = return ()

logHelper :: Debug -> Text -> [String] -> LaTeX ()
logHelper debug text extra =
  when (debug `elem` debugs) $ do
    lift $ T.putStrLn $ T.pack (show debug ++ ": ") <+>
      "'" <+> text <+> "' " <+>
      if null extra
         then T.empty
         else "(" <+> T.pack (unwords extra) <+> ")"

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

nl :: Text
nl = "%\n"

-- | A command that is used when two tokens are put next to each other
-- in the same column.

agdaSpace :: Text
agdaSpace = cmdPrefix <+> "Space" <+> cmdArg T.empty <+> nl

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
ptOpen' name = "\\>[" <+> name <+> "]"

-- | Opens the given column.

ptOpen :: AlignmentColumn -> Text
ptOpen c = ptOpen' (columnName c)

-- | Opens a special column that is only used at the beginning of
-- lines.

ptOpenBeginningOfLine :: Text
ptOpenBeginningOfLine = ptOpen' "." <+> "[@{}l@{}]"

-- | Opens the given column, and inserts an indentation instruction
-- with the given argument at the end of it.

ptOpenIndent
  :: AlignmentColumn
  -> Int              -- ^ Indentation instruction argument.
  -> Text
ptOpenIndent c delta =
  ptOpen c <+> "[@{}l@{"
           <+> cmdPrefix
           <+> "Indent"
           <+> cmdArg (T.pack $ show delta)
           <+> "}]"

ptClose :: Text
ptClose = "\\<"

ptClose' :: AlignmentColumn -> Text
ptClose' c =
  ptClose <+> "[" <+> columnName c <+> "]"

ptNL :: Text
ptNL = nl <+> "\\\\\n"

ptEmptyLine :: Text
ptEmptyLine =
  nl <+> "\\\\["
     <+> cmdPrefix
     <+> "EmptyExtraSkip"
     <+> "]%\n"

cmdPrefix :: Text
cmdPrefix = "\\Agda"

cmdArg :: Text -> Text
cmdArg x = "{" <+> x <+> "}"

------------------------------------------------------------------------
-- * Output generation from a stream of labelled tokens.

processLayers :: [(LayerRole, Tokens)] -> LaTeX ()
processLayers = mapM_ $ \(layerRole,toks) -> do
  case layerRole of
    L.Markup  -> processMarkup  toks
    L.Comment -> processComment toks
    L.Code    -> processCode    toks

processMarkup, processComment, processCode :: Tokens -> LaTeX ()

-- | Deals with markup, which is output verbatim.
processMarkup = mapM_ $ \t -> do
  moveColumnForToken t
  output (Text (text t))

-- | Deals with literate text, which is output verbatim
processComment = mapM_ $ \t -> do
  unless ("%" == T.take 1 (T.stripStart (text t))) $ do
    moveColumnForToken t
  output (Text (text t))

-- | Deals with code blocks. Every token, except spaces, is pretty
-- printed as a LaTeX command.
processCode toks' = do
  output $ Text nl
  enterCode
  mapM_ go toks'
  ptOpenWhenColumnZero =<< gets column
  output $ Text $ ptClose <+> nl
  leaveCode

  where
    go tok' = do
      -- Get the column information before grabbing the token, since
      -- grabbing (possibly) moves the column.
      col  <- gets column

      moveColumnForToken tok'
      let tok = text tok'
      log Code tok

      if (tok == T.empty) then return ()
      else do
        if (isSpaces tok) then do
            spaces $ T.group $ replaceSpaces tok
        else do
          ptOpenWhenColumnZero col
          output $ Text $
            -- we return the escaped token wrapped in commands corresponding
            -- to its aspect (if any) and other aspects (e.g. error, unsolved meta)
            foldr (\c t -> cmdPrefix <+> T.pack c <+> cmdArg t)
                  (escape tok)
                  $ map fromOtherAspect (toList $ otherAspects $ info tok') ++
                    concatMap fromAspect (toList $ aspect $ info tok')

    -- Non-whitespace tokens at the start of a line trigger an
    -- alignment column.
    ptOpenWhenColumnZero col =
        when (col == 0) $ do
          registerColumnZero
          output . Text . ptOpen =<< columnZero

    -- Translation from OtherAspect to command strings. So far it happens
    -- to correspond to @show@ but it does not have to (cf. fromAspect)
    fromOtherAspect :: OtherAspect -> String
    fromOtherAspect = show

    fromAspect :: Aspect -> [String]
    fromAspect a = let s = [show a] in case a of
      Comment           -> s
      Keyword           -> s
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
          Bound                     -> s
          Generalizable             -> s
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
        where
        s = show kind

-- | Escapes special characters.
escape :: Text -> Text
escape (T.uncons -> Nothing)     = T.empty
escape (T.uncons -> Just (c, s)) = T.pack (replace c) <+> escape s
  where
  replace :: Char -> String
  replace c = case c of
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
    _    -> [ c ]
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
    output . Text . ptOpen =<< columnZero
  output $ Text $ ptClose <+> ptNL <+>
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
  then log' Spaces "col /= 0"
  else do
    columns    <- gets columnsPrev
    codeBlock  <- gets codeBlock

    log' Spaces $
      "col == 0: " ++ show (len, columns)

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
  leadingSpaces t = [pre, suf]
    where (pre , suf) = T.span isSpaceNotNewline t

stringLiteral t = [t]

------------------------------------------------------------------------
-- * Main.

defaultStyFile :: String
defaultStyFile = "agda.sty"

-- | Generates a LaTeX file for the given interface.
--
-- The underlying source file is assumed to match the interface, but
-- this is not checked. TODO: Fix this problem, perhaps by storing the
-- source code in the interface.
generateLaTeX :: Interface -> TCM ()
generateLaTeX i = do
  let mod = toTopLevelModuleName $ iModuleName i
      hi  = iHighlighting i
  options <- TCM.commandLineOptions
  dir <-
    if O.optGHCiInteraction options
      then do
             sourceFile <- Find.srcFilePath <$> Find.findFile mod
             return $ filePath (projectRoot sourceFile mod) </> O.optLaTeXDir options
      else
             return $ O.optLaTeXDir options
  liftIO $ createDirectoryIfMissing True dir
  (code, _, _) <-
    liftIO $
      readProcessWithExitCode
        "kpsewhich"
        ["--path=" ++ dir, defaultStyFile]
        ""
  when (code /= ExitSuccess) $ do
    TCM.reportS
      "compile.latex"
      1
      [ defaultStyFile
          ++ " was not found. Copying a default version of "
          ++ defaultStyFile,
        "into " ++ dir ++ "."
      ]
    liftIO $ do
      styFile <- getDataFileName defaultStyFile
      liftIO $ copyFile styFile (dir </> defaultStyFile)
  let outPath = modToFile mod
  inAbsPath <- fmap filePath (Find.srcFilePath <$> Find.findFile mod)
  liftIO $ do
    latex <-
      E.encodeUtf8
        `fmap` toLaTeX (O.optCountClusters $ O.optPragmaOptions options)
                       (mkAbsolute inAbsPath)
                       (iSource i)
                       hi
    createDirectoryIfMissing True $ dir </> takeDirectory outPath
    BS.writeFile (dir </> outPath) latex

 where
  modToFile :: TopLevelModuleName -> FilePath
  modToFile m = List.intercalate [pathSeparator] (List1.toList $ moduleNameParts m) <.> "tex"

groupByFst :: forall a b. Eq a => [(a,b)] -> [(a,[b])]
groupByFst =
    map (\xs -> case xs of                     -- Float the grouping to the top level
          []           -> __IMPOSSIBLE__
          (tag, _): _ -> (tag, map snd xs))

  . List.groupBy ((==) `on` fst)  -- Group together characters in the same
                                  -- role.

-- | Transforms the source code into LaTeX.
toLaTeX
  :: Bool
     -- ^ Count extended grapheme clusters?
  -> AbsolutePath
  -> L.Text
  -> HighlightingInfo
  -> IO L.Text
toLaTeX cc path source hi =

  processTokens cc

    . map
      ( ( \(role, tokens) ->
            (role,) $
              -- This bit fixes issue 954
              ( if L.isCode role
                  then-- Remove trailing whitespace from the
                  -- final line; the function spaces
                  -- expects trailing whitespace to be
                  -- followed by a newline character.
                    whenMoreThanOne
                      ( withLast
                          $ withTokenText
                          $ \suf ->
                            maybe
                              suf
                              (T.dropWhileEnd isSpaceNotNewline)
                              (T.stripSuffix "\n" suf)
                      )
                      . withLast (withTokenText $ T.dropWhileEnd isSpaceNotNewline)
                      . withFirst
                        ( withTokenText $
                            \pre ->
                              fromMaybe pre $ T.stripPrefix "\n" $
                                T.dropWhile
                                  isSpaceNotNewline
                                  pre
                        )
                  else-- do nothing
                    id
              )
                tokens
        ) . ( second
                ( -- Split tokens at newlines
                  concatMap
                    ( stringLiteral
                        . ( \(mi, cs) ->
                              Token {text = T.pack cs, info = fromMaybe mempty mi}
                          )
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
              atomizeLayers . literateTeX (startPos (Just path))

  $ L.unpack source
  where
  infoMap = toMap (decompress hi)

  -- | This function preserves laziness of the list
  withLast :: (a -> a) -> [a] -> [a]
  withLast f [] = []
  withLast f [a] = [f a]
  withLast f (a:as) = a:withLast f as

  -- | This function preserves laziness of the list
  withFirst :: (a -> a) -> [a] -> [a]
  withFirst _ [] = []
  withFirst f (a:as) = f a:as

  whenMoreThanOne :: ([a] -> [a]) -> [a] -> [a]
  whenMoreThanOne f xs@(_:_:_) = f xs
  whenMoreThanOne _ xs         = xs



processTokens
  :: Bool
     -- ^ Count extended grapheme clusters?
  -> [(LayerRole, Tokens)]
  -> IO L.Text
processTokens cc ts = do
  ((), s, os) <- runLaTeX (processLayers ts) () (emptyState cc)
  return $ L.fromChunks $ map (render s) os
  where
    render _ (Text s)        = s
    render s (MaybeColumn c)
      | Just i <- columnKind c,
        not (Set.member i (usedColumns s)) = agdaSpace
      | otherwise                          = nl <+> ptOpen c
