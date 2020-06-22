module Agda.Compiler.Treeless.AsPatterns (recoverAsPatterns) where

import Control.Monad.Reader

import Agda.Syntax.Treeless

data AsPat = AsPat Int QName [Int]  -- x@(c ys)
  deriving (Show)

wk :: Int -> AsPat -> AsPat
wk n (AsPat x c ys) = AsPat (n + x) c (map (n +) ys)

type S = Reader [AsPat]

runS :: S a -> a
runS m = runReader m []

underBinds :: Int -> S a -> S a
underBinds 0 = id
underBinds n = local (map $ wk n)

bindAsPattern :: AsPat -> S a -> S a
bindAsPattern p = local (p :)

lookupAsPattern :: QName -> [TTerm] -> S TTerm
lookupAsPattern c vs
  | Just xs <- allVars vs = do
    ps <- ask
    case [ x | AsPat x c' ys <- ps, c == c', xs == ys ] of
      x : _ -> pure $ TVar x
      _     -> pure $ mkTApp (TCon c) vs
  | otherwise = pure $ mkTApp (TCon c) vs
  where
    allVars = mapM getVar
    getVar (TVar x) = Just x
    getVar _        = Nothing   -- what about erased?

-- | We lose track of @-patterns in the internal syntax. This pass puts them
--   back.
recoverAsPatterns :: Monad m => TTerm -> m TTerm
recoverAsPatterns t = return $ runS (recover t)

recover :: TTerm -> S TTerm
recover t =
  case t of
    TApp f vs -> do
      f  <- recover f
      vs <- mapM recover vs
      tApp f vs
    TLam b -> TLam <$> underBinds 1 (recover b)
    TCon{} -> tApp t []   -- need to recover nullary constructors as well (to make deep @-patterns work)
    TLet v b -> TLet <$> recover v <*> underBinds 1 (recover b)
    TCase x ct d bs -> TCase x ct <$> recover d <*> mapM (recoverAlt x) bs
    TCoerce t -> TCoerce <$> recover t
    TLit{}    -> pure t
    TVar{}    -> pure t
    TPrim{}   -> pure t
    TDef{}    -> pure t
    TUnit{}   -> pure t
    TSort{}   -> pure t
    TErased{} -> pure t
    TError{}  -> pure t

recoverAlt :: Int -> TAlt -> S TAlt
recoverAlt x b =
  case b of
    TACon c n b -> TACon c n <$> underBinds n (bindAsPattern (AsPat (x + n) c [n - 1, n - 2..0]) $ recover b)
    TAGuard g b -> TAGuard <$> recover g <*> recover b
    TALit l b   -> TALit l <$> recover b

tApp :: TTerm -> [TTerm] -> S TTerm
tApp (TCon c) vs = lookupAsPattern c vs
tApp f vs        = pure $ mkTApp f vs

