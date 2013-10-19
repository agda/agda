{-# LANGUAGE FlexibleInstances #-}

module Agda.Syntax.Internal.Pattern where

import Control.Applicative
import Control.Monad.State

import Agda.Syntax.Common -- hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Internal hiding (Arg)
import qualified Agda.Syntax.Internal as I

import Agda.Utils.List (downFrom)
import Agda.Utils.Monad ((<.>))
import Agda.Utils.Permutation
import Agda.Utils.Size (size)
import Agda.Utils.Tuple

-- * Tools for patterns

instance IsProjP Pattern where
  isProjP (ProjP d) = Just d
  isProjP _         = Nothing

patternsToElims :: Permutation -> [I.Arg Pattern] -> [Elim]
patternsToElims perm ps = evalState (mapM build ps) xs
  where
    xs   = permute (invertP perm) $ downFrom (size perm)

    tick :: State [Int] Int
    tick = do x : xs <- get; put xs; return x

    build :: I.Arg Pattern -> State [Int] Elim
    build (Arg ai (VarP _)     ) = Apply . Arg ai . var <$> tick
    build (Arg ai (ConP c _ ps)) =
      Apply . Arg ai . Con c <$> mapM (argFromElim <.> build) ps
    build (Arg ai (DotP t)     ) = Apply (Arg ai t) <$ tick
    build (Arg ai (LitP l)     ) = return $ Apply $ Arg ai $ Lit l
    build (Arg ai (ProjP dest) ) = return $ Proj  $ dest

-- * One hole patterns

-- | A @OneholePattern@ is a linear pattern context @P@ such that for
--   any non-projection pattern @p@, inserting @p@ into the single hole @P[p]@,
--   yields again a non-projection pattern.
data OneHolePatterns = OHPats [I.Arg Pattern] (I.Arg OneHolePattern) [I.Arg Pattern]
  deriving (Show)
data OneHolePattern  = Hole
		     | OHCon ConHead ConPatternInfo OneHolePatterns
                       -- ^ The type in 'ConPatternInfo' serves the same role as in 'ConP'.
                       --
                       -- TODO: If a hole is plugged this type may
                       -- have to be updated in some way.
  deriving (Show)

plugHole :: Pattern -> OneHolePatterns -> [I.Arg Pattern]
plugHole p (OHPats ps hole qs) = ps ++ [fmap (plug p) hole] ++ qs
  where
    plug p Hole           = p
    plug p (OHCon c mt h) = ConP c mt $ plugHole p h

-- | @allHoles ps@ returns for each pattern variable @x@ in @ps@ a
--   context @P@ such @P[x]@ is one of the patterns of @ps@.
--   The @Ps@ are returned in the left-to-right order of the
--   pattern variables in @ps@.
allHoles :: [I.Arg Pattern] -> [OneHolePatterns]
allHoles = map snd . allHolesWithContents

allHolesWithContents :: [I.Arg Pattern] -> [(Pattern, OneHolePatterns)]
allHolesWithContents []       = []
allHolesWithContents (p : ps) = map left phs ++ map (right p) (allHolesWithContents ps)
  where
    phs :: [(Pattern, I.Arg OneHolePattern)]
    phs = map (id -*- setHiding (getHiding p) . defaultArg)
              (holes $ unArg p)

    holes :: Pattern -> [(Pattern, OneHolePattern)]
    holes p@(VarP _)     = [(p, Hole)]
    holes p@(DotP _)     = [(p, Hole)]
    holes (ConP c mt qs) = map (id -*- OHCon c mt) $ allHolesWithContents qs
    holes LitP{}         = []
    holes ProjP{}        = []

    left  (p, ph)               = (p, OHPats [] ph ps)
    right q (p, OHPats ps h qs) = (p, OHPats (q : ps) h qs)
