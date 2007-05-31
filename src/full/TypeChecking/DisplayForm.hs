{-# OPTIONS -cpp #-}

module TypeChecking.DisplayForm where

import Control.Applicative
import Control.Monad
import Control.Monad.Error

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute

#include "../undefined.h"

displayForm :: QName -> Args -> TCM (Maybe DisplayTerm)
displayForm c vs = do
    df <- defDisplay <$> getConstInfo c
    return $ matchDisplayForm df vs
  `catchError` \_ -> return Nothing

matchDisplayForm :: DisplayForm -> Args -> Maybe DisplayTerm
matchDisplayForm NoDisplay       _  = Nothing
matchDisplayForm (Display n ps v) vs
  | length ps > length vs = Nothing
  | otherwise             = do
    us <- match n ps $ raise 1 (map unArg vs0)
    return $ substs (reverse us) v `apply` vs1
  where
    (vs0, vs1) = splitAt (length ps) vs

class Match a where
  match :: Nat -> a -> a -> Maybe [Term]

instance Match a => Match [a] where
  match n xs ys = concat <$> zipWithM (match n) xs ys

instance Match a => Match (Arg a) where
  match n p v = match n (unArg p) (unArg v)

instance Match Term where
  match n p v = case (p, v) of
    (Var 0 [], v)                  -> return [subst __IMPOSSIBLE__ v]
    (Var i ps, Var j vs) | i == j  -> match n ps vs
    (Def c ps, Def d vs) | c == d  -> match n ps vs
    (Con c ps, Con d vs) | c == d  -> match n ps vs
    (Lit l, Lit l')      | l == l' -> return []
    (p, v)               | p == v  -> return []
    _                              -> fail ""

