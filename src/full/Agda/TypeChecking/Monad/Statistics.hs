{-# OPTIONS_GHC -Wunused-imports #-}

-- | Collect statistics.

module Agda.TypeChecking.Monad.Statistics
    ( MonadStatistics(..), tick, tickN, tickMax, getStatistics, modifyStatistics, printStatistics
    ) where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Trans.Maybe

import qualified Data.Map as Map
import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug

import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty
import Agda.Utils.String

class ReadTCState m => MonadStatistics m where
  modifyCounter :: String -> (Integer -> Integer) -> m ()

  default modifyCounter
    :: (MonadStatistics n, MonadTrans t, t n ~ m)
    =>  String -> (Integer -> Integer) -> m ()
  modifyCounter x = lift . modifyCounter x

instance MonadStatistics m => MonadStatistics (ExceptT e m)
instance MonadStatistics m => MonadStatistics (MaybeT m)
instance MonadStatistics m => MonadStatistics (ReaderT r m)
instance MonadStatistics m => MonadStatistics (StateT  s m)
instance (MonadStatistics m, Monoid w) => MonadStatistics (WriterT w m)

instance MonadStatistics TCM where
  modifyCounter x f = modifyStatistics $ force . update
    where
      -- We need to be strict in the map.
      -- Andreas, 2014-03-22:  Could we take Data.Map.Strict instead of this hack?
      -- Or force the map by looking up the very element we inserted?
      -- force m = Map.lookup x m `seq` m
      -- Or use insertLookupWithKey?
      -- update m = old `seq` m' where
      --   (old, m') = Map.insertLookupWithKey (\ _ new old -> f old) x dummy m
      -- Ulf, 2018-04-10: Neither of these approaches are strict enough in the
      -- map (nor are they less hacky). It's not enough to be strict in the
      -- values stored in the map, we also need to be strict in the *structure*
      -- of the map. A less hacky solution is to deepseq the map.
      force m = rnf m `seq` m
      update  = Map.insertWith (\ new old -> f old) x dummy
      dummy   = f 0

-- | Get the statistics.
getStatistics :: ReadTCState m => m Statistics
getStatistics = useR stStatistics

-- | Modify the statistics via given function.
modifyStatistics :: (Statistics -> Statistics) -> TCM ()
modifyStatistics f = stStatistics `modifyTCLens` f

-- | Increase specified counter by @1@.
tick :: MonadStatistics m => String -> m ()
tick x = tickN x 1

-- | Increase specified counter by @n@.
tickN :: MonadStatistics m => String -> Integer -> m ()
tickN s n = modifyCounter s (n +)

-- | Set the specified counter to the maximum of its current value and @n@.
tickMax :: MonadStatistics m => String -> Integer -> m ()
tickMax s n = modifyCounter s (max n)

-- | Print the given statistics.
printStatistics
  :: (MonadDebug m, MonadTCEnv m, HasOptions m)
  => Maybe TopLevelModuleName -> Statistics -> m ()
printStatistics mmname stats = do
  unlessNull (Map.toList stats) $ \ stats -> do
    let -- First column (left aligned) is accounts.
        col1 = Boxes.vcat Boxes.left  $ map (Boxes.text . fst) stats
        -- Second column (right aligned) is numbers.
        col2 = Boxes.vcat Boxes.right $ map (Boxes.text . showThousandSep . snd) stats
        table = Boxes.hsep 1 Boxes.left [col1, col2]
    reportSLn "" 1 $ caseMaybe mmname "Accumulated statistics" $ \ mname ->
      "Statistics for " ++ prettyShow mname
    reportSLn "" 1 $ Boxes.render table
