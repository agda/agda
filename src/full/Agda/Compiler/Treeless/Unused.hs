
module Agda.Compiler.Treeless.Unused
  ( usedArguments
  , stripUnusedArguments
  ) where

import Control.Arrow (first)
import Control.Applicative
import qualified Data.Map as Map

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Pretty

usedArguments :: TTerm -> [Bool]
usedArguments t = [ Map.member i fv | i <- reverse [0..n - 1] ]
  where
    (n, b) = lamView t
    fv     = freeVars b

stripUnusedArguments :: [Bool] -> TTerm -> TTerm
stripUnusedArguments used t = unlamView m $ applySubst rho b
  where
    (n, b) = lamView t
    m      = length $ filter id used'
    used'  = reverse $ take n $ used ++ repeat True
    rho = computeSubst used'
    computeSubst (False : bs) = TErased :# computeSubst bs
    computeSubst (True  : bs) = liftS 1 $ computeSubst bs
    computeSubst []           = idS

lamView :: TTerm -> (Int, TTerm)
lamView (TLam b) = first succ $ lamView b
lamView t        = (0, t)

unlamView :: Int -> TTerm -> TTerm
unlamView 0 t = t
unlamView n t = TLam $ unlamView (n - 1) t
