
module Agda.Compiler.Treeless.Identity
  ( detectIdentityFunctions ) where

import Prelude hiding ((!!))  -- don't use partial functions

import Control.Applicative ( Alternative((<|>), empty) )
import Data.Semigroup
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List as List

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad

import Agda.Utils.List

import Agda.Utils.Impossible

detectIdentityFunctions :: QName -> TTerm -> TCM TTerm
detectIdentityFunctions q t =
  case isIdentity q t of
    Nothing     -> return t
    Just (n, k) -> do
      markInline True q
      def <- theDef <$> getConstInfo q
      return $ mkTLam n $ TVar k

-- If isIdentity f t = Just (n, k) then
-- f = t is equivalent to f = λ xn₋₁ .. x₀ → xk
isIdentity :: QName -> TTerm -> Maybe (Int, Int)
isIdentity q t =
  trivialIdentity q t <|> recursiveIdentity q t

-- Does the function recurse on an argument, rebuilding the same value again.
recursiveIdentity :: QName -> TTerm -> Maybe (Int, Int)
recursiveIdentity q t =
  case b of
    TCase x _ (TError TUnreachable) bs
      | all (identityBranch x) bs -> pure (n, x)
    _ -> empty -- TODO: lets?
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

        proj x args = indexWithDefault __IMPOSSIBLE__ (reverse args) x

        match TErased              _  = True
        match (TVar z)             y = z == y
        match (TApp (TDef f) args) y = f == q && length args == n && match (proj x args) y
        match _                    _ = False

data IdentityIn = IdIn [Int]

notId :: IdentityIn
notId = IdIn []

instance Semigroup IdentityIn where
  IdIn xs <> IdIn ys = IdIn $ List.intersect xs ys

-- Does the function always return one of its arguments unchanged (possibly
-- through recursive calls).
trivialIdentity :: QName -> TTerm -> Maybe (Int, Int)
trivialIdentity q t =
  case go 0 b of
    IdIn [x]     -> pure (n, x)
    IdIn []      -> Nothing
    IdIn (_:_:_) -> Nothing  -- only happens for empty functions (which will never be called)
  where
    (n, b) = tLamView t

    go :: Int -> TTerm -> IdentityIn
    go k t =
      case t of
        TVar x | x >= k    -> IdIn [x - k]
               | otherwise -> notId
        TLet _ b           -> go (k + 1) b
        TCase _ _ d bs     -> sconcat (go k d :| map (goAlt k) bs)
        TApp (TDef f) args
          | f == q         -> IdIn [ y | (TVar x, y) <- zip (reverse args) [0..], y + k == x ]
        TCoerce v          -> go k v
        TApp{}             -> notId
        TLam{}             -> notId
        TLit{}             -> notId
        TDef{}             -> notId
        TCon{}             -> notId
        TPrim{}            -> notId
        TUnit{}            -> notId
        TSort{}            -> notId
        TErased{}          -> notId
        TError{}           -> notId

    goAlt :: Int -> TAlt -> IdentityIn
    goAlt k (TALit _ b)   = go k b
    goAlt k (TAGuard _ b) = go k b
    goAlt k (TACon _ n b) = go (k + n) b
