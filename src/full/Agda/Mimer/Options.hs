module Agda.Mimer.Options where

import Data.Char
import Data.Maybe
import Text.Read

import Agda.Interaction.BasicOps (parseExprIn)
import Agda.Syntax.Common (Nat)
import Agda.Syntax.Common.Pretty (Pretty, pretty, text)
import Agda.Syntax.Abstract.Name (QName)
import Agda.TypeChecking.Monad.Base (TCM)
import Agda.Interaction.Highlighting.Range (empty)
import Agda.Syntax.Common (InteractionId)
import Agda.Syntax.Position (Range)
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Name as AN
import Agda.Utils.Maybe (catMaybes)

type MilliSeconds = Integer

data HintMode = Unqualified | AllModules | Module | NoHints
  deriving (Eq, Show)

data Options = Options
  { optTimeout :: MilliSeconds
  , optHintMode :: HintMode
  , optSkip :: Int  -- ^ Skip the first this many solutions
  , optList :: Bool -- ^ List solutions instead of filling the hole
  , optExplicitHints :: [QName]
  } deriving Show

parseOptions :: InteractionId -> Range -> String -> TCM Options
parseOptions ii range argStr = do
  let tokens = readTokens $ words argStr
  -- TODO: Use 'parseName' instead?
  hintExprs <- sequence [parseExprIn ii range h | H h <- tokens]
  let hints = catMaybes $ map hintExprToQName hintExprs
  return Options
    { optTimeout = firstOr 1000 [fromIntegral $ parseTime t | T t <- tokens]
    -- TODO: Do arg properly
    , optHintMode = firstOr NoHints ([Module | M <- tokens] ++ [Unqualified | U <- tokens])
    , optExplicitHints = hints
    , optList = L `elem` tokens
    , optSkip = firstOr 0 [ n | S s <- tokens, n <- maybeToList $ readMaybe s ]
    }

parseTime :: String -> Int
parseTime [] = 0
parseTime xs = read ds * modifier + parseTime r where
  (ds , modr) = span isDigit xs
  (mod , r)   = break isDigit modr

  modifier = case mod of
    "ms" -> 1
    "cs" -> 10
    "ds" -> 100
    "s"  -> 1000
    _    -> 1000

hintExprToQName :: A.Expr -> Maybe QName
hintExprToQName (A.ScopedExpr _ e) = hintExprToQName e
hintExprToQName (A.Def qname)      = Just $ qname
hintExprToQName (A.Proj _ qname)   = Just $ AN.headAmbQ qname
hintExprToQName (A.Con qname)      = Just $ AN.headAmbQ qname
hintExprToQName _ = Nothing

firstOr :: a -> [a] -> a
firstOr x [] = x
firstOr _ (x:_) = x


data Token = T String | M | U | C | L | S String | H String
  deriving (Eq, Show)

readTokens :: [String] -> [Token]
readTokens []              = []
readTokens ("-t" : t : ws) = T t : readTokens ws
readTokens ("-s" : n : ws) = S n : readTokens ws
readTokens ("-l"     : ws) = L   : readTokens ws
readTokens ("-m"     : ws) = M   : readTokens ws
readTokens ("-c"     : ws) = C   : readTokens ws
readTokens ("-u"     : ws) = U   : readTokens ws
readTokens (h        : ws) = H h : readTokens ws

instance Pretty HintMode where
  pretty = text . show

-- instance Pretty Options where
--   prettyht
