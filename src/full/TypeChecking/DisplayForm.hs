
module TypeChecking.DisplayForm where

import Control.Applicative

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute

displayForm :: MonadTCM tcm => QName -> Args -> tcm (Maybe DisplayTerm)
displayForm c vs = do
  df <- defDisplay <$> getConstInfo c
  return $ matchDisplayForm df vs

matchDisplayForm :: DisplayForm -> Args -> Maybe DisplayTerm
matchDisplayForm NoDisplay       _  = Nothing
matchDisplayForm (Display n ps v) vs
  | length ps > length vs = Nothing
  | otherwise             = do
    us <- match ps $ map unArg vs0
    return $ substs us v `apply` vs1
  where
    (vs0, vs1) = splitAt (length ps) vs

-- | Arguments have the same length.
match :: [Term] -> [Term] -> Maybe [Term]
match _ _ = Nothing

