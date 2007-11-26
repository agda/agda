
module Syntax.Internal.Pattern where

import Syntax.Common
import Syntax.Internal

data OneHolePatterns = OHPats [Arg Pattern] (Arg OneHolePattern) [Arg Pattern]
data OneHolePattern  = Hole
		     | OHCon QName OneHolePatterns

plugHole :: Pattern -> OneHolePatterns -> [Arg Pattern]
plugHole p (OHPats ps hole qs) = ps ++ [fmap (plug p) hole] ++ qs
  where
    plug p Hole	       = p
    plug p (OHCon c h) = ConP c $ plugHole p h

allHoles :: [Arg Pattern] -> [OneHolePatterns]
allHoles [] = []
allHoles (p : ps) = map left phs ++ map right (allHoles ps)
  where
    phs :: [Arg OneHolePattern]
    phs = map (Arg $ argHiding p) (holes $ unArg p)

    holes :: Pattern -> [OneHolePattern]
    holes (VarP _)    = [Hole]
    holes (DotP _)    = [Hole]
    holes (ConP c qs) = map (OHCon c) $ allHoles qs
    holes _	      = []

    left  ph		   = OHPats [] ph ps
    right (OHPats ps h qs) = OHPats (p : ps) h qs


