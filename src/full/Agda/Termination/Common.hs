{- | Utilities that are used by type-based and syntax-based termination checkers
     Extracted to a separate module so that they both can use the utilities without the need to depend on each other -}
{-# LANGUAGE NondecreasingIndentation #-}
module Agda.Termination.Common where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Statistics
import Agda.TypeChecking.Monad.Debug
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import qualified Data.Set as Set
import Data.Set ( Set )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad.Env
import Agda.Syntax.Translation.InternalToAbstract
import qualified Agda.Utils.SmallSet as SmallSet
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Signature
import Data.Maybe
import Control.Applicative
import Agda.Termination.Order
import Agda.Termination.CallMatrix
import qualified Agda.Termination.SparseMatrix as Matrix
import qualified Data.List as List

-- | Try to get rid of a function call targeting the current SCC
--   using a non-recursive clause.
--
--   This can help copattern definitions of dependent records.
tryReduceNonRecursiveClause
  :: (MonadTCM m, MonadDebug m, MonadStatistics m) =>
     QName                 -- ^ Function
  -> Elims                 -- ^ Arguments
  -> Set QName
  -> (Term -> m a)  -- ^ Continue here if we managed to reduce.
  -> m a            -- ^ Otherwise, continue here.
  -> m a
tryReduceNonRecursiveClause g es mutuals continue fallback = do
  -- Andreas, 2020-02-06, re: issue #906
  let v0 = Def g es
  reportSDoc "term.reduce" 40 $ "Trying to reduce away call: " <+> prettyTCM v0

  -- First, make sure the function is in the current SCC.
  if (notElem g mutuals) then fallback else do
  reportSLn "term.reduce" 40 $ "This call is in the current SCC!"

  -- Then, collect its non-recursive clauses.
  cls <- liftTCM $ getNonRecursiveClauses g
  reportSLn "term.reduce" 40 $ unwords [ "Function has", show (length cls), "non-recursive exact clauses"]
  reportSDoc "term.reduce" 80 $ vcat $ map (prettyTCM . NamedClause g True) cls
  reportSLn  "term.reduce" 80 . ("allowed reductions = " ++) . show . SmallSet.elems
    =<< asksTC envAllowedReductions

  -- Finally, try to reduce with the non-recursive clauses (and no rewrite rules).
  r <- liftTCM $ modifyAllowedReductions (SmallSet.delete UnconfirmedReductions) $
    runReduceM $ appDefE' g v0 cls [] (map notReduced es)
  case r of
    NoReduction{}    -> fallback
    YesReduction _ v -> do
      reportSDoc "term.reduce" 30 $ vcat
        [ "Termination checker: Successfully reduced away call:"
        , nest 2 $ prettyTCM v0
        ]
      verboseS "term.reduce" 5 $ tick "termination-checker-reduced-nonrecursive-call"
      continue v

getNonRecursiveClauses :: QName -> TCM [Clause]
getNonRecursiveClauses q =
  filter (liftA2 (&&) nonrec exact) . defClauses <$> getConstInfo q
  where
  nonrec = maybe False not . clauseRecursive
  exact  = fromMaybe False . clauseExact

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: Int -> Int -> [[Order]] -> CallMatrix
makeCM ncols nrows matrix = CallMatrix $
  Matrix.fromLists (Matrix.Size nrows ncols) matrix

buildRecCallLocation :: MonadTCM m => QName -> Elims -> m (Closure Term)
buildRecCallLocation qname elims =
  -- Andreas, 2013-05-19 as pointed out by Andrea Vezzosi,
  -- printing the call eagerly is forbiddingly expensive.
  -- So we build a closure such that we can print the call
  -- whenever we really need to.
  -- This saves 30s (12%) on the std-lib!
  -- Andreas, 2015-01-21 Issue 1410: Go to the module where g is defined
  -- otherwise its free variables with be prepended to the call
  -- in the error message.

  -- Andreas, 2018-07-22, issue #3136
  -- Dropping only inserted arguments at the end, since
  -- dropping arguments in the middle might make the printer crash.
  -- Def g $ filter ((/= Inserted) . getOrigin) es0
  -- Andreas, 2017-01-05, issue #2376
  -- Remove arguments inserted by etaExpandClause.
  liftTCM $ withCurrentModule (qnameModule qname) $
   buildClosure $ Def qname $ List.dropWhileEnd ((Inserted ==) . getOrigin) elims
