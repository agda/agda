
module Agda.Compiler.MAlonzo.Coerce (addCoercions) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute
import Agda.Utils.Functor

-- | Insert unsafeCoerce (in the form of 'TCoerce') everywhere it's needed in
--   the right-hand side of a definition.
addCoercions :: TTerm -> TCM TTerm
addCoercions = coerceTop
  where
    -- Don't coerce top-level lambdas.
    coerceTop (TLam b) = TLam <$> coerceTop b
    coerceTop t        = coerce t

    -- Coerce a term `t`. The result (when translated to Haskell) has type
    -- `forall a. a`.
    coerce t =
      case t of
        TVar{}    -> return $ TCoerce t
        TPrim{}   -> return $ TCoerce t
        TDef{}    -> return $ TCoerce t
        TCon{}    -> return $ TCoerce t
        TLit{}    -> return $ TCoerce t
        TUnit{}   -> return $ TCoerce t
        TSort{}   -> return $ TCoerce t
        TErased{} -> return t
        TCoerce{} -> return t
        TError{}  -> return t
        TApp f vs -> do
          ar <- funArity f
          if length vs > ar
            then TApp (TCoerce f) <$> mapM softCoerce vs
            else TCoerce . TApp f <$> mapM coerce vs
        TLam b         -> TCoerce . TLam <$> softCoerce b
        TLet e b       -> TLet <$> softCoerce e <*> coerce b
        TCase x t d bs -> TCase x t <$> coerce d <*> mapM coerceAlt bs

    coerceAlt a = coerce (aBody a) <&> \ b -> a { aBody = b }

    -- Insert TCoerce in subterms. When translated to Haskell, the resulting
    -- term is well-typed with some type arbitrary type.
    softCoerce t =
      case t of
        TVar{}    -> return t
        TPrim{}   -> return t
        TDef{}    -> return t
        TCon{}    -> return t
        TLit{}    -> return t
        TUnit{}   -> return t
        TSort{}   -> return t
        TErased{} -> return t
        TCoerce{} -> return t
        TError{}  -> return t
        TApp f vs -> do
          ar <- funArity f
          if length vs > ar
            then TApp (TCoerce f) <$> mapM softCoerce vs
            else TApp f <$> mapM coerce vs
        TLam b         -> TLam <$> softCoerce b
        TLet e b       -> TLet <$> softCoerce e <*> softCoerce b
        TCase x t d bs -> TCase x t <$> coerce d <*> mapM coerceAlt bs

funArity :: TTerm -> TCM Int
funArity (TDef q)  = maybe 0 (fst . tLamView) <$> getTreeless q
funArity (TCon q)  = length . filter not <$> getErasedConArgs q
funArity (TPrim _) = return 3 -- max arity of any primitive
funArity _         = return 0

