
module Syntax.Internal.Pattern where

import Syntax.Common
import Syntax.Internal
import Utils.Tuple

data OneHolePatterns = OHPats [Arg Pattern] (Arg OneHolePattern) [Arg Pattern]
  deriving (Show)
data OneHolePattern  = Hole
		     | OHCon QName OneHolePatterns
  deriving (Show)

plugHole :: Pattern -> OneHolePatterns -> [Arg Pattern]
plugHole p (OHPats ps hole qs) = ps ++ [fmap (plug p) hole] ++ qs
  where
    plug p Hole	       = p
    plug p (OHCon c h) = ConP c $ plugHole p h

allHoles :: [Arg Pattern] -> [OneHolePatterns]
allHoles = map snd . allHolesWithContents

allHolesWithContents :: [Arg Pattern] -> [(Pattern, OneHolePatterns)]
allHolesWithContents []       = []
allHolesWithContents (p : ps) = map left phs ++ map (right p) (allHolesWithContents ps)
  where
    phs :: [(Pattern, Arg OneHolePattern)]
    phs = map (id -*- Arg (argHiding p)) (holes $ unArg p)

    holes :: Pattern -> [(Pattern, OneHolePattern)]
    holes p@(VarP _)  = [(p, Hole)]
    holes p@(DotP _)  = [(p, Hole)]
    holes (ConP c qs) = map (id -*- OHCon c) $ allHolesWithContents qs
    holes _           = []

    left  (p, ph)               = (p, OHPats [] ph ps)
    right q (p, OHPats ps h qs) = (p, OHPats (q : ps) h qs)


