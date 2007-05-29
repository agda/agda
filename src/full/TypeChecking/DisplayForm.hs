
module TypeChecking.DisplayForm where

import Syntax.Internal
import TypeChecking.Monad.Base
import TypeChecking.Substitute

matchDisplayForm :: QName -> DisplayForm -> Args -> DisplayTerm
matchDisplayForm c (Display n ps v) vs
  | length ps > length vs = def
  | otherwise             = case match ps vs0 of
    Just us -> substs us v `apply` vs1
    Nothing -> DTerm def
  where
    (vs0, vs1) = splitAt (length ps) vs
    def = Def c vs
