
module Agda.Compiler.Treeless.Identity
  ( detectIdentityFunctions ) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad

detectIdentityFunctions :: QName -> TTerm -> TCM TTerm
detectIdentityFunctions q t =
  case isIdentity q t of
    Nothing     -> return t
    Just (n, k) -> do
      markInline q
      return $ mkTLam n $ TVar k
  return $ detectId q t

-- If isIdentity f t = Just (n, k) then
-- f = t is equivalent to f = λ xₙ₋₁ .. x₀ → xk
isIdentity :: QName -> TTerm -> Maybe (Int, Int)
isIdentity q t = Nothing
