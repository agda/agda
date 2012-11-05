{-# LANGUAGE CPP, ViewPatterns #-}

-- | Function for generating highlighted and aligned LaTeX from literate
-- Agda source.

module Agda.Interaction.Highlighting.LaTeX
  ( generateLaTeX
  ) where

import Data.Char
import Data.Maybe
import Data.Function
import Data.List
import Control.Monad.RWS
import Control.Monad.Error
import Control.Monad.Trans
import System.Directory
import System.FilePath
import System.Process
import System.Exit
import Data.Text (Text)
import qualified Data.Text          as T
import qualified Data.Text.Encoding as E
import qualified Data.ByteString    as BS

import qualified Data.List as List
import qualified Data.Map  as Map

import Paths_Agda

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import Agda.Interaction.Highlighting.Precise
import Agda.TypeChecking.Monad (TCM)
import qualified Agda.TypeChecking.Monad as TCM
import Agda.Interaction.Options
import Agda.Compiler.CallCompiler
import qualified Agda.Utils.IO.UTF8 as UTF8

#include "../../undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Datatypes.

-- | The @LaTeX@ monad is a combination of @ErrorT@ and @RWS@. The error
-- part is just used to keep track whether we finished or not, the
-- reader part isn't used, the writer is where the output goes and the
-- state is for keeping track of the tokens and some other useful info.
type LaTeX = ErrorT String (RWS () Text State)

data State = State
  { tokens     :: Tokens
  , column     :: Int     -- ^ Column number, used for polytable alignment.
  , indent     :: Int     -- ^ Indentation level, also for alignment.
  , indentPrev :: Int
  , inCode     :: Bool    -- ^ Keeps track of whether we are in a code
                          -- block or not.
  }

type Tokens = [Token]

data Token = Token
  { string   :: Text
  , info     :: MetaInfo
  , position :: Integer  -- ^ Is not used currently, but could
                         -- potentially be used for hyperlinks as in
                         -- the HTML output?
  }

-- | Run function for the @LaTeX@ monad.
runLaTeX :: LaTeX a -> () -> State -> (Either String a, State, Text)
runLaTeX = runRWS . runErrorT

emptyState :: State
emptyState = State
  { tokens     = []
  , column     = 0
  , indent     = 0
  , indentPrev = 0
  , inCode     = False
  }

------------------------------------------------------------------------
-- * Some helpers.

(<+>) = T.append

isInfixOf' :: Text -> Text -> Maybe (Text, Text)
isInfixOf' needle haystack = go (T.tails haystack) 0
  where
  go []                                         n = Nothing
  go ((T.stripPrefix needle -> Just suf) : xss) n = Just (T.take n haystack, suf)
  go (_                                  : xss) n = go xss (n + 1)

isSpaces :: Text -> Bool
isSpaces (T.uncons -> Nothing)     = True
isSpaces (T.uncons -> Just (c, s)) | isSpace c = isSpaces s
                                   | otherwise = False

isSpaces _                         = __IMPOSSIBLE__

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
    t : ts | string t == beginCode || string t == endCode ||
             T.singleton '%' == T.take 1 (T.stripStart (string t)) -> do

      modify $ \s -> s { tokens = ts }
      return t

    t : ts -> do
      modify $ \s -> s { tokens = ts }

      inCode <- gets inCode
      let code = if inCode then endCode else beginCode

      case code `isInfixOf'` string t of
        Nothing -> do

          -- Spaces take care of their own column tracking.
          unless (isSpaces (string t)) $ do
            moveColumn $ T.length $ string t

          return t

        Just (pre, suf) -> do
          let t'  = t { string = code }
          let t'' = t { string = suf }
          modify $ \s -> s { tokens = t' : t'' : tokens s }

          unless (isSpaces pre) $ do
            moveColumn $ T.length pre

          return $ t { string = pre }

nextToken :: LaTeX Text
nextToken = string `fmap` nextToken'

resetColumn :: LaTeX ()
resetColumn = modify $ \s -> s { column = 0 }

moveColumn :: Int -> LaTeX ()
moveColumn i = modify $ \s -> s { column = i + column s }

moveIndent :: Int -> LaTeX ()
moveIndent i = modify $ \s -> s { indent = i + indent s }

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

------------------------------------------------------------------------
-- * LaTeX and polytable strings.

-- Polytable, http://www.ctan.org/pkg/polytable, is used for code
-- alignment, similar to lhs2TeX's approach.

nl        = T.pack "%\n"
beginCode = T.pack "\\begin{code}"
endCode   = T.pack "\\end{code}"

ptOpen     = T.pack "\\>"
ptOpen'  i = ptOpen <+> T.pack ("[" ++ show i ++ "]")
ptClose    = T.pack "\\<"
ptClose' i = ptClose <+> T.pack ("[" ++ show i ++ "]")
ptNL       = nl <+> T.pack "\\\\\n"

cmdPrefix   = T.pack "\\Agda"
cmdArg    x = T.singleton '{' <+> x <+> T.singleton '}'
cmdIndent i = cmdPrefix <+> T.pack "Indent" <+>
                  cmdArg (T.pack (show i)) <+> cmdArg T.empty

infixl'     = T.pack "infixl"
infix'      = T.pack "infix"
infixr'     = T.pack "infixr"

------------------------------------------------------------------------
-- * Automaton.

-- | The start state, @nonCode@, prints non-code (the LaTeX part of
-- literate Agda) until it sees a @beginBlock@.
nonCode :: LaTeX ()
nonCode = do
  tok <- nextToken

  if tok == beginCode

     then do
       tell tok
       resetColumn
       setInCode
       code

     else do
       tell tok
       nonCode

-- | Deals with code blocks. Every token, except spaces, is pretty
-- printed as a LaTeX command.
code :: LaTeX ()
code = do

  col <- gets column
  when (col == 0) $ do
    tell ptOpen

  tok' <- nextToken'
  let tok = string tok'

  when (tok == endCode) $ do
    tell $ ptClose <+> tok
    unsetInCode
    nonCode

  when (tok `elem` [ infixl', infix', infixr' ]) $ do
    tell $ cmdPrefix <+> T.pack "Keyword" <+> cmdArg tok
    fixity
    code

  when (isSpaces tok) $ do
    spaces $ T.group tok
    code

  case aspect (info tok') of
    Nothing -> tell $ escape tok
    Just a  -> tell $ cmdPrefix <+> T.pack (cmd a) <+> cmdArg (escape tok)
  code

  where
  cmd :: Aspect -> String
  cmd (Name mKind _) = maybe __IMPOSSIBLE__ showKind mKind
    where
    showKind :: NameKind -> String
    showKind (Constructor Inductive)   = "InductiveConstructor"
    showKind (Constructor CoInductive) = "CoinductiveConstructor"
    showKind k                         = show k
  cmd a              = show a

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
    '~'  -> "\textasciitilde"
    '^'  -> "\textasciicircum"
    '\\' -> "\textbackslash"
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
        tell $ cmdPrefix <+> T.pack "Number" <+> cmdArg num
        fixity

    -- Operations followed by newlines.
    (ops, nls) | otherwise      -> do
        tell $ escape ops
        spaces (T.group nls)


-- | Spaces are grouped before processed, because multiple consecutive
-- spaces determine the alignment of the code and consecutive newline
-- characters need special treatment as well.
spaces :: [Text] -> LaTeX ()
spaces []                                 = return ()
spaces ((T.uncons -> Nothing)       : ss) = __IMPOSSIBLE__

-- Single spaces are ignored.
spaces ((T.uncons -> Just (' ', s)) : []) | T.null s = do
  moveColumn 1
  tell $ T.singleton ' '

-- Multiple spaces.
spaces (s@(T.uncons -> Just (' ', _)) : ss) = do
  let len = T.length s

  col <- gets column
  moveColumn len

  if col == 0
     then do

       -- FIX: What's going on here?
       ind     <- gets indent
       indPrev <- gets indentPrev

       if ind == len
          then do
            tell $ ptOpen' indPrev
          else do
            if len < ind
               then do
                 resetIndent
                 resetIndentPrev
                 tell $ ptOpen' $ if indPrev == 0 ||
                                         len == indPrev
                                     then 0
                                     else ind - indPrev - len
               else do
                 moveIndent $ len - ind
                 setIndentPrev ind
                 tell $ ptOpen' ind

       tell $ cmdIndent len
       tell $ ptClose' len <+> nl <+> ptOpen' len
     else do
       tell $ T.singleton ' '
       col <- gets column
       tell $ ptClose' col <+> nl <+> ptOpen' col

  spaces ss

-- Newlines.
spaces (s@(T.uncons -> Just ('\n', _)) : ss) = do
  resetColumn
  tell $ ptClose <+> T.replicate (T.length s) ptNL
  spaces ss

-- Treat tabs as if they were spaces.
spaces (s@(T.uncons -> Just ('\t', _)) : ss) =
  spaces $ T.replicate (T.length s) (T.singleton ' ') : ss
spaces (_                              : ss) = __IMPOSSIBLE__

------------------------------------------------------------------------
-- * Main.

defaultStyFile = "agda.sty"

-- | The only exported function. It's (only) called in @Main.hs@.
generateLaTeX :: A.ModuleName -> HighlightingInfo -> TCM ()
generateLaTeX mod hi = do

  options <- TCM.commandLineOptions

  -- There is a default directory given by 'defaultLaTeXDir'.
  let dir = optLaTeXDir options
  liftIO $ createDirectoryIfMissing True dir

  TCM.reportSLn "latex" 1 $ unlines
    [ ""
    , "Checking if " ++ defaultStyFile ++ " is found by the LaTeX environment."
    ]

  merrors <- callCompiler' "kpsewhich" [ defaultStyFile ]

  when (isJust merrors) $ do
    TCM.reportSLn "latex" 1 $ unlines
      [ ""
      , defaultStyFile ++ " was not found. Copying a default version of " ++
          defaultStyFile
      , "into the working directory."
      ]

    liftIO $ do
      styFile <- getDataFileName defaultStyFile
      liftIO $ copyFile styFile defaultStyFile

  liftIO $ do
    source <- UTF8.readTextFile (modToFile mod <.> "lagda")
    let latex = E.encodeUtf8 $ toLaTeX source hi
    BS.writeFile (dir </> modToFile mod <.> "tex") latex

  where
  modToFile :: A.ModuleName -> FilePath
  modToFile mod = go $ show mod
    where
    go []         = []
    go ('.' : cs) = pathSeparator : go cs
    go (c   : cs) = c             : go cs

-- | Transforms the source code into LaTeX.
toLaTeX :: String -> HighlightingInfo -> Text
toLaTeX source hi

  = processTokens

  -- Head the list (the grouped chars contain the same meta info) and
  -- collect the characters into a string.
  . map (\xs -> case xs of
                    (mi, (pos, _)) : _ ->
                        Token { string   = T.pack $ map (\(_, (_, c)) -> c) xs
                              , info     = maybe mempty id mi
                              , position = pos
                              }
                    []                 -> __IMPOSSIBLE__)

  . List.groupBy ((==) `on` fst)  -- Characters which share the same
                                  -- meta info are the same token, so
                                  -- group them together.

  -- Look up the meta info at each position in the highlighting info.
  . map (\(pos, char) ->
        (Map.lookup pos infoMap, (pos, char)))

  -- Add position in file to each character.
  . zip [1..]
  $ source
  where
  infoMap = toMap (decompress hi)

processTokens :: Tokens -> Text
processTokens ts =
  case x of
    Left "Done" -> s
    _           -> __IMPOSSIBLE__
  where
  (x, _, s) = runLaTeX nonCode () (emptyState { tokens = ts })
