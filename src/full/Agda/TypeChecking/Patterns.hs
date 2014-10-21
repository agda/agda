-- RETIRED (Andreas, 2013-10-19)

-- | Pattern utils which need the TCM monad.
module Agda.TypeChecking.Patterns where

import Control.Applicative
import Control.Monad.State

import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (Arg)
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Datatypes

import Agda.Utils.List (downFrom)
import Agda.Utils.Monad ((<.>))
import Agda.Utils.Permutation
import Agda.Utils.Size (size)

patternsToElims :: Permutation -> [I.Arg Pattern] -> TCM [Elim]
patternsToElims perm ps = evalStateT (mapM build ps) xs
  where
    xs   = permute (invertP __IMPOSSIBLE__ perm) $ downFrom (size perm)

    tick :: StateT [Int] TCM Int
    tick = do x : xs <- get; put xs; return x

    build :: I.Arg Pattern -> StateT [Int] TCM Elim
    build (Arg ai (VarP _)     ) = Apply . Arg ai . var <$> tick
    build (Arg ai (ConP c _ ps)) = do
      con <- lift $ getConHead $ conName c
      Apply . Arg ai . Con con <$> mapM (argFromElim <.> build) ps
    build (Arg ai (DotP t)     ) = Apply (Arg ai t) <$ tick
    build (Arg ai (LitP l)     ) = return $ Apply $ Arg ai $ Lit l
    build (Arg ai (ProjP dest) ) = return $ Proj  $ dest
