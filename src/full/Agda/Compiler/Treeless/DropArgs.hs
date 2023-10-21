{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Treeless.DropArgs ( dropArgs ) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad as I

dropArgs :: TTerm -> TCM TTerm
dropArgs t = return $ go t
  where
    isErasedAnnotated :: TTerm -> Bool
    isErasedAnnotated (TErased ErasedAnnotated) = True
    isErasedAnnotated _ = False

    go :: TTerm -> TTerm
    go t = case tAppView t of
      (h , vs) -> tApp h $ map go $ filter (not . isErasedAnnotated) vs

    tApp f []                  = f
    tApp (TErased i) _         = TErased i
    tApp f _ | isUnreachable f = tUnreachable
    tApp f es                  = mkTApp f es
