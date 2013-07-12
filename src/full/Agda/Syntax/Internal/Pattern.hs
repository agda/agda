{-# LANGUAGE FlexibleInstances #-}

module Agda.Syntax.Internal.Pattern where

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
-- import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Internal
import Agda.Utils.Tuple

-- * Tools for patterns

instance IsProjP Pattern where
  isProjP (ProjP d) = Just d
  isProjP _         = Nothing

-- * One hole patterns

-- | A @OneholePattern@ is a linear pattern context @P@ such that for
--   any non-projection pattern @p@, inserting @p@ into the single hole @P[p]@,
--   yields again a non-projection pattern.
data OneHolePatterns = OHPats [Arg Pattern] (Arg OneHolePattern) [Arg Pattern]
  deriving (Show)
data OneHolePattern  = Hole
		     | OHCon QName ConPatternInfo OneHolePatterns
                       -- ^ The type in 'ConPatternInfo' serves the same role as in 'ConP'.
                       --
                       -- TODO: If a hole is plugged this type may
                       -- have to be updated in some way.
  deriving (Show)

plugHole :: Pattern -> OneHolePatterns -> [Arg Pattern]
plugHole p (OHPats ps hole qs) = ps ++ [fmap (plug p) hole] ++ qs
  where
    plug p Hole           = p
    plug p (OHCon c mt h) = ConP c mt $ plugHole p h

-- | @allHoles ps@ returns for each pattern variable @x@ in @ps@ a
--   context @P@ such @P[x]@ is one of the patterns of @ps@.
--   The @Ps@ are returned in the left-to-right order of the
--   pattern variables in @ps@.
allHoles :: [Arg Pattern] -> [OneHolePatterns]
allHoles = map snd . allHolesWithContents

allHolesWithContents :: [Arg Pattern] -> [(Pattern, OneHolePatterns)]
allHolesWithContents []       = []
allHolesWithContents (p : ps) = map left phs ++ map (right p) (allHolesWithContents ps)
  where
    phs :: [(Pattern, Arg OneHolePattern)]
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
