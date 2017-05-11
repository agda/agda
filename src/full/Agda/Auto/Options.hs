module Agda.Auto.Options where

import Control.Monad.State
import Agda.Utils.Lens

data Mode = MNormal Bool Bool -- true if list mode, true if disprove

          | MCaseSplit

          | MRefine Bool -- true if list mode


data AutoHintMode = AHMNone
                  | AHMModule

type Hints = [String]

newtype TimeOut = TimeOut { getTimeOut :: Int }

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
  , autoTimeOut  = TimeOut 1
  , autoPick     = 0
  , autoMode     = MNormal False False
  , autoHintMode = AHMNone
  }

aoHints :: Lens' Hints AutoOptions
aoHints f s =
  f (autoHints s) <&>
  \x -> s {autoHints = x}

aoTimeOut :: Lens' TimeOut AutoOptions
aoTimeOut f s =
  f (autoTimeOut s) <&>
  \x -> s {autoTimeOut = x}

aoPick :: Lens' Int AutoOptions
aoPick f s =
  f (autoPick s) <&>
  \x -> s {autoPick = x}

aoMode :: Lens' Mode AutoOptions
aoMode f s =
  f (autoMode s) <&>
  \x -> s {autoMode = x}

aoHintMode :: Lens' AutoHintMode AutoOptions
aoHintMode f s =
  f (autoHintMode s) <&>
  \x -> s {autoHintMode = x}

-- | Tokenising the input (makes `parseArgs` cleaner)

data AutoToken =
    M | C | R | D | L
  | T Int | S Int | H String

autoTokens :: [String] -> [AutoToken]
autoTokens []              = []
autoTokens ("-t" : t : ws) = T (read t) : autoTokens ws
autoTokens ("-s" : s : ws) = S (read s) : autoTokens ws
autoTokens ("-l"     : ws) = L          : autoTokens ws
autoTokens ("-d"     : ws) = D          : autoTokens ws
autoTokens ("-m"     : ws) = M          : autoTokens ws
autoTokens ("-c"     : ws) = C          : autoTokens ws
autoTokens ("-r"     : ws) = R          : autoTokens ws
autoTokens (h        : ws) = H h        : autoTokens ws

parseArgs :: String -> AutoOptions
parseArgs s = mapM_ step (autoTokens $ words s)
              `execState` initAutoOptions where

  step :: AutoToken -> State AutoOptions ()
  step M     = aoHintMode .= AHMModule
  step C     = aoMode     .= MCaseSplit
  step R     = aoPick     .= (-1)
            >> aoMode     .= MRefine False
  step (T t) = aoTimeOut  .= TimeOut t
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
