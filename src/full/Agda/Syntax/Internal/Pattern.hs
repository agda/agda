{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverlappingInstances   #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}  -- because of func. deps.

module Agda.Syntax.Internal.Pattern where

import Control.Applicative
import Control.Monad.State

import Data.Maybe
import Data.Traversable (traverse)

import Agda.Syntax.Common as Common hiding (NamedArg)
import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Internal hiding (Arg)
import qualified Agda.Syntax.Internal as I

import Agda.Utils.List
import Agda.Utils.Functor ((<.>))
import Agda.Utils.Permutation
import Agda.Utils.Size (size)
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- * Tools for clauses

-- | Translate the clause patterns to terms with free variables bound by the
--   clause telescope.
--
--   Precondition: no projection patterns.
clauseArgs :: Clause -> Args
clauseArgs cl = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ clauseElims cl

-- | Translate the clause patterns to an elimination spine
--   with free variables bound by the clause telescope.
clauseElims :: Clause -> Elims
clauseElims cl = patternsToElims (clausePerm cl) (namedClausePats cl)

-- | Arity of a function, computed from clauses.
class FunArity a where
  funArity :: a -> Int

-- | Get the number of initial 'Apply' patterns.
instance IsProjP p => FunArity [p] where
  funArity = length . takeWhile (isNothing . isProjP)

-- | Get the number of initial 'Apply' patterns in a clause.
instance FunArity Clause where
  funArity = funArity . clausePats

-- | Get the number of common initial 'Apply' patterns in a list of clauses.
instance FunArity [Clause] where
  funArity []  = 0
  funArity cls = minimum $ map funArity cls

-- * Tools for patterns

-- | Label the pattern variables from left to right
--   using one label for each variable pattern and one for each dot pattern.
class LabelPatVars a b i | b -> i where
  labelPatVars :: a -> State [i] b
  -- ^ Intended, but unpractical due to the absence of type-level lambda, is:
  --   @labelPatVars :: f (Pattern' x) -> State [i] (f (Pattern' (i,x)))@

instance LabelPatVars a b i => LabelPatVars (Arg c a) (Arg c b) i where
  labelPatVars = traverse labelPatVars

instance LabelPatVars a b i => LabelPatVars (Named x a) (Named x b) i where
  labelPatVars = traverse labelPatVars

instance LabelPatVars a b i => LabelPatVars [a] [b] i where
  labelPatVars = traverse labelPatVars

instance LabelPatVars (Pattern' x) (Pattern' (i,x)) i where
  labelPatVars p =
    case p of
      VarP x       -> VarP . (,x) <$> next
      DotP t       -> DotP t <$ next
      ConP c mt ps -> ConP c mt <$> labelPatVars ps
      LitP l       -> return $ LitP l
      ProjP q      -> return $ ProjP q
    where next = do (x:xs) <- get; put xs; return x

-- | Augment pattern variables with their de Bruijn index.
{-# SPECIALIZE numberPatVars :: Permutation -> [NamedArg (Pattern' x)] -> [(NamedArg (Pattern' (Int, x)))] #-}
numberPatVars :: LabelPatVars a b Int => Permutation -> a -> b
numberPatVars perm ps = evalState (labelPatVars ps) $
  permute (invertP __IMPOSSIBLE__ perm) $ downFrom $ size perm

instance IsProjP Pattern where
  isProjP (ProjP d) = Just d
  isProjP _         = Nothing

patternsToElims :: Permutation -> [I.NamedArg Pattern] -> [Elim]
patternsToElims perm ps = map build' $ numberPatVars perm ps
  where

    build' :: NamedArg (Pattern' (Int, PatVarName)) -> Elim
    build' = build . fmap namedThing

    build :: I.Arg (Pattern' (Int, PatVarName)) -> Elim
    build (Arg ai (VarP (i, _))) = Apply $ Arg ai $ var i
    build (Arg ai (ConP c _ ps)) = Apply $ Arg ai $ Con c $
      map (argFromElim . build') ps
    build (Arg ai (DotP t)     ) = Apply $ Arg ai t
    build (Arg ai (LitP l)     ) = Apply $ Arg ai $ Lit l
    build (Arg ai (ProjP dest) ) = Proj  $ dest

-- patternsToElims :: Permutation -> [I.NamedArg Pattern] -> [Elim]
-- patternsToElims perm ps = evalState (mapM build' ps) xs
--   where
--     xs   = permute (invertP __IMPOSSIBLE__ perm) $ downFrom (size perm)

--     tick :: State [Int] Int
--     tick = do x : xs <- get; put xs; return x

--     build' :: NamedArg Pattern -> State [Int] Elim
--     build' = build . fmap namedThing

--     build :: I.Arg Pattern -> State [Int] Elim
--     build (Arg ai (VarP _)     ) = Apply . Arg ai . var <$> tick
--     build (Arg ai (ConP c _ ps)) =
--       Apply . Arg ai . Con c <$> mapM (argFromElim <.> build') ps
--     build (Arg ai (DotP t)     ) = Apply (Arg ai t) <$ tick
--     build (Arg ai (LitP l)     ) = return $ Apply $ Arg ai $ Lit l
--     build (Arg ai (ProjP dest) ) = return $ Proj  $ dest

-- * One hole patterns

-- | A @OneholePattern@ is a linear pattern context @P@ such that for
--   any non-projection pattern @p@, inserting @p@ into the single hole @P[p]@,
--   yields again a non-projection pattern.
data OneHolePatterns = OHPats [NamedArg Pattern]
                              (NamedArg OneHolePattern)
                              [NamedArg Pattern]
  deriving (Show)
data OneHolePattern  = Hole
                     | OHCon ConHead ConPatternInfo OneHolePatterns
                       -- ^ The type in 'ConPatternInfo' serves the same role as in 'ConP'.
                       --
                       -- TODO: If a hole is plugged this type may
                       -- have to be updated in some way.
  deriving (Show)

plugHole :: Pattern -> OneHolePatterns -> [NamedArg Pattern]
plugHole p (OHPats ps hole qs) = ps ++ [fmap (plug p <$>) hole] ++ qs
  where
    plug p Hole           = p
    plug p (OHCon c mt h) = ConP c mt $ plugHole p h

-- | @allHoles ps@ returns for each pattern variable @x@ in @ps@ a
--   context @P@ such @P[x]@ is one of the patterns of @ps@.
--   The @Ps@ are returned in the left-to-right order of the
--   pattern variables in @ps@.
allHoles :: [NamedArg Pattern] -> [OneHolePatterns]
allHoles = map snd . allHolesWithContents

allHolesWithContents :: [NamedArg Pattern] -> [(Pattern, OneHolePatterns)]
allHolesWithContents []       = []
allHolesWithContents (p : ps) = map left phs ++ map (right p) (allHolesWithContents ps)
  where
    phs :: [(Pattern, NamedArg OneHolePattern)]
    phs = map (id -*- \h -> fmap (h <$) p)
              (holes $ namedArg p)

    holes :: Pattern -> [(Pattern, OneHolePattern)]
    holes p@(VarP _)     = [(p, Hole)]
    holes p@(DotP _)     = [(p, Hole)]
    holes (ConP c mt qs) = map (id -*- OHCon c mt) $ allHolesWithContents qs
    holes LitP{}         = []
    holes ProjP{}        = []

    left  (p, ph)               = (p, OHPats [] ph ps)
    right q (p, OHPats ps h qs) = (p, OHPats (q : ps) h qs)
