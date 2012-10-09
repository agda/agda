{-# LANGUAGE CPP, PatternGuards, TypeSynonymInstances, FlexibleInstances #-}
module Agda.TypeChecking.ProjectionLike where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free (isBinderUsed)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.CompiledClause
-- import Agda.TypeChecking.CompiledClause.Compile

import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation
import Agda.Utils.Pretty

#include "../undefined.h"
import Agda.Utils.Impossible


-- | Turn a definition into a projection if it looks like a projection.
makeProjection :: QName -> TCM ()
makeProjection x = inContext [] $ do
  reportSLn "tc.proj.like" 30 $ "Considering " ++ show x ++ " for projection likeness"
  defn <- getConstInfo x
  case theDef defn of
    -- Constructor-headed functions can't be projection-like (at the moment). The reason
    -- for this is that invoking constructor-headedness will circumvent the inference of
    -- the dropped arguments.
    -- Nor can abstract definitions be projection-like since they won't reduce
    -- outside the abstract block.
    def@Function{funProjection = Nothing, funClauses = cls, funCompiled = cc0, funInv = NotInjective,
                 funMutual = [], -- Andreas, 2012-09-28: only consider non-mutual funs (or those whose recursion status has not yet been determined)
                 funAbstr = ConcreteDef} -> do
      ps0 <- filterM validProj (candidateArgs [] (unEl $ defType defn))
      reportSLn "tc.proj.like" 30 $ if null ps0 then "  no candidates found"
                                                else "  candidates: " ++ show ps0
      unless (null ps0) $ do
      -- Andreas 2012-09-26: only consider non-recursive functions for proj.like.
      -- Issue 700: problems with recursive funs. in term.checker and reduction
      ifM recursive (reportSLn "tc.proj.like" 30 $ "recursive functions are not considered for projection-likeness") $ do
      ps <- return $ filter (checkOccurs cls . snd) ps0
      when (not (null ps0) && null ps) $ reportSLn "tc.proj.like" 50 $ "  occurs check failed\n    clauses = " ++ show cls
      case reverse ps of
        []         -> return ()
        (d, n) : _ -> do
          reportSLn "tc.proj.like" 10 $ show (defName defn) ++ " is projection like in argument " ++
                                        show n ++ " for type " ++ show d
          let cls' = map (dropArgs n) cls
              cc   = dropArgs n cc0
          -- cc <- compileClauses (Just (x, __IMPOSSIBLE__)) cls'
          reportSLn "tc.proj.like" 20 $ "  rewrote clauses to\n    " ++ show cc
          let newDef = def
                       { funProjection     = Just (d, n + 1)
                       , funClauses        = cls'
                       , funCompiled       = cc
                       , funInv            = dropArgs n $ funInv def
                       }
          addConstant x $ defn { defPolarity       = drop n $ defPolarity defn
                               , defArgOccurrences = drop n $ defArgOccurrences defn
                               , defDisplay        = []
                               , theDef            = newDef
                               }
    Function{funInv = Inverse{}} ->
      reportSLn "tc.proj.like" 30 $ "  injective functions can't be projections"
    Function{funAbstr = AbstractDef} ->
      reportSLn "tc.proj.like" 30 $ "  abstract functions can't be projections"
    Function{funProjection = Just{}} ->
      reportSLn "tc.proj.like" 30 $ "  already projection like"
    _ -> reportSLn "tc.proj.like" 30 $ "  not a function"
  where
    -- @validProj (d,n)@ checks whether the head @d@ of the type of the
    -- @n@th argument is injective in all args (i.d. being name of data/record/axiom).
    validProj :: (QName, Int) -> TCM Bool
    validProj (_, 0) = return False
    validProj (d, _) = do
      defn <- theDef <$> getConstInfo d
      return $ case defn of
        Datatype{} -> True
        Record{}   -> True
        Axiom{}    -> True
        _          -> False

    recursive = do
      occs <- computeOccurrences x
      let xocc = Map.lookup (ADef x) occs
      case xocc of
        Just (_ : _) -> return True -- recursive occurrence
        _            -> return False

    checkOccurs cls n = all (nonOccur n) cls

    nonOccur n Clause{clausePerm = Perm _ p, clausePats = ps, clauseBody = b} =
      and [ take n p == [0..n - 1]
          , onlyMatch n ps  -- projection-like functions are only allowed to match on the eliminatee
                            -- otherwise we may end up projecting from constructor applications, in
                            -- which case we can't reconstruct the dropped parameters
          , checkBody n b ]

    onlyMatch n ps = all (shallowMatch . unArg) (take 1 ps1) &&
                       noMatches (ps0 ++ drop 1 ps1)
      where
        (ps0, ps1) = splitAt n ps
        shallowMatch (ConP _ _ ps) = noMatches ps
        shallowMatch _             = True
        noMatches = all (noMatch . unArg)
        noMatch ConP{} = False
        noMatch LitP{} = False
        noMatch VarP{} = True
        noMatch DotP{} = True

    checkBody 0 _          = True
    checkBody _ NoBody     = False    -- absurd clauses are not permitted
    checkBody n (Bind b)   = not (isBinderUsed b) && checkBody (n - 1) (unAbs b)
    checkBody _ Body{}     = __IMPOSSIBLE__

    -- @candidateArgs [var 0,...,var(n-1)] t@ adds @(n,d)@ to the output,
    -- if @t@ is a function-type with domain @t 0 .. (n-1)@
    -- (the domain of @t@ is the type of the arg @n@).
    --
    -- This means that from the type of arg @n@ all previous arguments
    -- can be computed by a simple matching.
    -- (Provided the @d@ is data/record/postulate, checked in @validProj@).
    --
    -- E.g. f : {x : _}(y : _){z : _} -> D x y z -> ...
    -- will return (D,3) as a candidate (amongst maybe others).
    --
    candidateArgs :: [Term] -> Term -> [(QName,Int)]
    candidateArgs vs (Shared p) = candidateArgs vs $ derefPtr p
    candidateArgs vs (Pi (Dom r h (El _ def)) b)
      | Def d us <- ignoreSharing def,
        vs == map unArg us = (d, length vs) : candidateRec vs b
    candidateArgs vs (Pi _ b) = candidateRec vs b
    candidateArgs _ _ = []

    candidateRec vs NoAbs{} = []
    candidateRec vs b       = candidateArgs (var (size vs) : vs) (unEl $ absBody b)

---------------------------------------------------------------------------
-- * Dropping initial arguments to create a projection-like function
---------------------------------------------------------------------------

-- | When making a function projection-like, we drop the first @n@
--   arguments.
class DropArgs a where
  dropArgs :: Int -> a -> a

-- | NOTE: This creates telescopes with unbound de Bruijn indices.
instance DropArgs Telescope where
  dropArgs n tel = telFromList $ drop n $ telToList tel

instance DropArgs Permutation where
  dropArgs n (Perm m p) = Perm (m - n) $ map (subtract n) $ drop n p

-- | NOTE: does not go into the body, so does not work for recursive functions.
instance DropArgs ClauseBody where
  dropArgs 0 b        = b
  dropArgs _ NoBody   = NoBody
  dropArgs n (Bind b) = dropArgs (n - 1) (absBody b)
  dropArgs n Body{}   = __IMPOSSIBLE__

-- | NOTE: does not work for recursive functions.
instance DropArgs Clause where
  dropArgs n cl =
      cl{ clausePerm = dropArgs n $ clausePerm cl
        , clauseTel  = dropArgs n $ clauseTel cl
          -- Andreas, 2012-09-25: just dropping the front of telescope
          -- makes it ill-formed (unbound indices)
          -- we should let the telescope intact!?
        , clausePats = drop n $ clausePats cl
        , clauseBody = dropArgs n $ clauseBody cl -- BUG: need to drop also from recursive calls!!
        }

instance DropArgs FunctionInverse where
  dropArgs n finv = fmap (dropArgs n) finv

{- UNUSED, but don't remove (Andreas, 2012-10-08)
-- | Use for dropping initial lambdas in compiled clause bodies.
--   NOTE: does not reduce term, need lambdas to be present.
instance DropArgs Term where
  dropArgs 0 v = v
  dropArgs n v = case ignoreSharing v of
    Lam h b -> dropArgs (n - 1) (absBody b)
    _       -> __IMPOSSIBLE__
-}

-- | To drop the first @n@ arguments in a compiled clause,
--   we reduce the split argument indices by @n@ and
--   drop @n@ arguments from the bodies.
--   NOTE: this only works for non-recursive functions, we
--   are not dropping arguments to recursive calls in bodies.
instance DropArgs CompiledClauses where
  dropArgs n cc = case cc of
    Case i br | i < n         -> __IMPOSSIBLE__
              | otherwise     -> Case (i - n) $ fmap (dropArgs n) br
    Done xs t | length xs < n -> __IMPOSSIBLE__
              | otherwise     -> Done (drop n xs) t
    Fail                      -> Fail

