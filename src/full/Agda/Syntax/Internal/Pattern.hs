{-# LANGUAGE FlexibleInstances #-}

module Agda.Syntax.Internal.Pattern where

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal
import Agda.Utils.Tuple

data OneHolePatterns = OHPats [Arg Pattern] (Arg OneHolePattern) [Arg Pattern]
  deriving (Show)
data OneHolePattern  = Hole
		     | OHCon QName (Maybe (Arg Type)) OneHolePatterns
                       -- ^ The type serves the same role as the type
                       -- argument to 'ConP'.
                       --
                       -- TODO: If a hole is plugged this type may
                       -- have to be updated in some way.
  deriving (Show)

plugHole :: Pattern -> OneHolePatterns -> [Arg Pattern]
plugHole p (OHPats ps hole qs) = ps ++ [fmap (plug p) hole] ++ qs
  where
    plug p Hole           = p
    plug p (OHCon c mt h) = ConP c mt $ plugHole p h

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
    holes _              = []

    left  (p, ph)               = (p, OHPats [] ph ps)
    right q (p, OHPats ps h qs) = (p, OHPats (q : ps) h qs)
