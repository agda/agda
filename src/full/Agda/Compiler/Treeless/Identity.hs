
module Agda.Compiler.Treeless.Identity
  ( detectIdentityFunctions ) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad
import Agda.Utils.Lens

detectIdentityFunctions :: QName -> TTerm -> TCM TTerm
detectIdentityFunctions q t =
  case isIdentity q t of
    Nothing     -> return t
    Just (n, k) -> do
      markInline q
      def <- theDef <$> getConstInfo q
      return $ mkTLam n $ TVar k

-- If isIdentity f t = Just (n, k) then
-- f = t is equivalent to f = λ xₙ₋₁ .. x₀ → xk
isIdentity :: QName -> TTerm -> Maybe (Int, Int)
isIdentity q t =
  case b of
    TCase x _ (TError TUnreachable) bs
      | all (identityBranch x) bs -> Just (n, x)
    _ -> Nothing  -- TODO: lets?
  where
    (n, b) = tLamView t

    identityBranch _ TALit{}   = False
    identityBranch _ TAGuard{} = False
    identityBranch x (TACon c a b) =
      case b of
        TApp (TCon c') args -> c == c' && identityArgs a args
        TVar y              -> y == x + a  -- from @-pattern recovery
        _                   -> False -- TODO: nested cases
      where
        identityArgs a args =
          length args == a && and (zipWith match (reverse args) [0..])

        proj x args = reverse args !! x

        match TErased              _  = True
        match (TVar z)             y = z == y
        match (TApp (TDef f) args) y = f == q && length args == n && match (proj x args) y
        match _                    _ = False
