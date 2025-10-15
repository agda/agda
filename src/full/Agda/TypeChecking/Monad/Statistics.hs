{-# OPTIONS_GHC -Wunused-imports #-}

-- | Collect statistics.

module Agda.TypeChecking.Monad.Statistics
  ( MonadStatistics(..), tick, getStatistics, modifyStatistics, printStatistics
  ) where

import Control.DeepSeq ( NFData(rnf) )
import Control.Monad.Except ( ExceptT )
import Control.Monad.Reader ( ReaderT )
import Control.Monad.State ( StateT )
import Control.Monad.Writer ( WriterT )
import Control.Monad.Trans.Class ( MonadTrans(lift) )
import Control.Monad.Trans.Maybe ( MaybeT )

import qualified Data.HashMap.Strict as HMap
import Data.Semigroup ( Max(..), Sum(..) )
import Data.Coerce ( coerce )

import Data.List ( sortOn )
import Data.Word ( Word64 )

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug ( MonadDebug, alwaysReportSLn )

import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Utils.String ( showThousandSep )
import Agda.Utils.Maybe ( caseMaybe )
import Agda.Utils.Null ( unlessNull )

class ReadTCState m => MonadStatistics m where
  tickN   :: String -> Word64 -> m ()
  tickMax :: String -> Word64 -> m ()

  default tickN :: (MonadStatistics n, MonadTrans t, t n ~ m) => String -> Word64 -> m ()
  tickN x = lift . tickN x

  default tickMax :: (MonadStatistics n, MonadTrans t, t n ~ m) => String -> Word64 -> m ()
  tickMax x = lift . tickMax x

instance MonadStatistics m => MonadStatistics (ExceptT e m)
instance MonadStatistics m => MonadStatistics (MaybeT m)
instance MonadStatistics m => MonadStatistics (ReaderT r m)
instance MonadStatistics m => MonadStatistics (StateT  s m)
instance (MonadStatistics m, Monoid w) => MonadStatistics (WriterT w m)

instance MonadStatistics TCM where
  tickN x n = modifyStatistics \case
    Statistics a b ->
      let a' = HMap.insertWith (<>) x (Sum n) a
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
      in rnf a' `seq` Statistics a' b

  tickMax x n = modifyStatistics \case
    Statistics a b ->
      let b' = HMap.insertWith (<>) x (Max n) b
       in rnf b' `seq` Statistics a b'

-- | Get the statistics.
getStatistics :: ReadTCState m => m Statistics
getStatistics = useR stStatistics

-- | Modify the statistics via given function.
modifyStatistics :: (Statistics -> Statistics) -> TCM ()
modifyStatistics f = stStatistics `modifyTCLens'` f

-- | Increase specified counter by @1@.
tick :: MonadStatistics m => String -> m ()
tick x = tickN x 1

-- | Print the given statistics.
printStatistics
  :: (MonadDebug m, MonadTCEnv m, HasOptions m)
  => Maybe TopLevelModuleName -> Statistics -> m ()
printStatistics mmname (Statistics tick max) = do
  let
    counters :: [(String, Word64)]
    counters = sortOn fst $ HMap.toList (coerce tick) <> HMap.toList (coerce max)

  unlessNull counters $ \ stats -> do
    let
      -- First column (left aligned) is accounts.
      col1 = Boxes.vcat Boxes.left  $ map (Boxes.text . fst) stats

      -- Second column (right aligned) is numbers.
      col2 = Boxes.vcat Boxes.right $ map (Boxes.text . showThousandSep . snd) stats

      table = Boxes.hsep 1 Boxes.left [col1, col2]

    alwaysReportSLn "" 1 $ caseMaybe mmname "Accumulated statistics" $ \ mname ->
      "Statistics for " ++ prettyShow mname

    alwaysReportSLn "" 1 $ Boxes.render table
