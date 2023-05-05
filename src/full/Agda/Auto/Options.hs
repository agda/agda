module Agda.Auto.Options where

import Data.Char
import Control.Monad.State
import Agda.Utils.Lens

data Mode = MNormal Bool Bool -- true if list mode, true if disprove

          | MCaseSplit

          | MRefine Bool -- true if list mode


data AutoHintMode = AHMNone
                  | AHMModule

type Hints = [String]

newtype TimeOut = TimeOut { getTimeOut :: Int } -- in ms

instance Show TimeOut where
  show = show . getTimeOut

-- | Options for Auto, default value and lenses

data AutoOptions = AutoOptions
  { autoHints    :: Hints
  , autoTimeOut  :: TimeOut
  , autoPick     :: Int
  , autoMode     :: Mode
  , autoHintMode :: AutoHintMode
  }

initAutoOptions :: AutoOptions
initAutoOptions = AutoOptions
  { autoHints    = []
  , autoTimeOut  = TimeOut 1000
  , autoPick     = 0
  , autoMode     = MNormal False False
  , autoHintMode = AHMNone
  }

aoHints :: Lens' AutoOptions Hints
aoHints f s =
  f (autoHints s) <&>
  \x -> s {autoHints = x}

aoTimeOut :: Lens' AutoOptions TimeOut
aoTimeOut f s =
  f (autoTimeOut s) <&>
  \x -> s {autoTimeOut = x}

aoPick :: Lens' AutoOptions Int
aoPick f s =
  f (autoPick s) <&>
  \x -> s {autoPick = x}

aoMode :: Lens' AutoOptions Mode
aoMode f s =
  f (autoMode s) <&>
  \x -> s {autoMode = x}

aoHintMode :: Lens' AutoOptions AutoHintMode
aoHintMode f s =
  f (autoHintMode s) <&>
  \x -> s {autoHintMode = x}

-- | Tokenising the input (makes `parseArgs` cleaner)

data AutoToken =
    M | C | R | D | L
  | T String | S Int | H String

autoTokens :: [String] -> [AutoToken]
autoTokens []              = []
autoTokens ("-t" : t : ws) = T t        : autoTokens ws
autoTokens ("-s" : s : ws) = S (read s) : autoTokens ws
autoTokens ("-l"     : ws) = L          : autoTokens ws
autoTokens ("-d"     : ws) = D          : autoTokens ws
autoTokens ("-m"     : ws) = M          : autoTokens ws
autoTokens ("-c"     : ws) = C          : autoTokens ws
autoTokens ("-r"     : ws) = R          : autoTokens ws
autoTokens (h        : ws) = H h        : autoTokens ws

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

parseArgs :: String -> AutoOptions
parseArgs s = mapM_ step (autoTokens $ words s)
              `execState` initAutoOptions where

  step :: AutoToken -> State AutoOptions ()
  step M     = aoHintMode .= AHMModule
  step C     = aoMode     .= MCaseSplit
  step R     = aoPick     .= (-1)
            >> aoMode     .= MRefine False
  step (T t) = aoTimeOut  .= TimeOut (parseTime t)
  step (S p) = aoPick     .= p
  step (H h) = aoHints    %= (h :)
  step D     = do
    mode <- use aoMode
    case mode of
      MNormal lm _ -> aoMode .= MNormal lm True
      _            -> return ()
  step L     = do
    mode <- use aoMode
    case mode of
      MNormal _ dp -> aoMode .= MNormal True dp
      MRefine _    -> aoMode .= MRefine True
      _            -> return ()
