-- | Collect statistics.

module Agda.TypeChecking.Monad.Statistics
    ( tick, tickN, tickMax, getStatistics, modifyStatistics, printStatistics
    ) where

import qualified Data.Map as Map

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Syntax.Concrete.Name as C

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.String

-- | Get the statistics.
getStatistics :: TCM Statistics
getStatistics = use stStatistics

-- | Modify the statistics via given function.
modifyStatistics :: (Statistics -> Statistics) -> TCM ()
modifyStatistics f = stStatistics %= f

-- | Increase specified counter by @1@.
tick :: String -> TCM ()
tick x = tickN x 1

-- | Increase specified counter by @n@.
tickN :: String -> Integer -> TCM ()
tickN s n = modifyCounter s (n +)

-- | Set the specified counter to the maximum of its current value and @n@.
tickMax :: String -> Integer -> TCM ()
tickMax s n = modifyCounter s (max n)

-- | Modify specified counter by a function @f@.
modifyCounter :: String -> (Integer -> Integer) -> TCM ()
modifyCounter x f = modifyStatistics $ force . update
  where
    -- We need to be strict in the map.
    -- Andreas, 2014-03-22:  Could we take Data.Map.Strict instead of this hack?
    -- Or force the map by looking up the very element we inserted?
    -- force m = Map.lookup x m `seq` m
    -- Or use insertLookupWithKey?
    -- update m = old `seq` m' where
    --   (old, m') = Map.insertLookupWithKey (\ _ new old -> f old) x dummy m
    force m = sum (Map.elems m) `seq` m
    update  = Map.insertWith (\ new old -> f old) x dummy
    dummy   = f 0

-- | Print the given statistics if verbosity "profile" is given.
printStatistics :: Int -> Maybe C.TopLevelModuleName -> Statistics -> TCM ()
printStatistics vl mmname stats = verboseS "profile" vl $ do
  unlessNull (Map.toList stats) $ \ stats -> do
    let -- First column (left aligned) is accounts.
        col1 = Boxes.vcat Boxes.left  $ map (Boxes.text . fst) stats
        -- Second column (right aligned) is numbers.
        col2 = Boxes.vcat Boxes.right $ map (Boxes.text . showThousandSep . snd) stats
        table = Boxes.hsep 1 Boxes.left [col1, col2]
    reportSLn "profile" 1 $ caseMaybe mmname "Accumlated statistics" $ \ mname ->
      "Statistics for " ++ prettyShow mname
    reportSLn "profile" 1 $ Boxes.render table
