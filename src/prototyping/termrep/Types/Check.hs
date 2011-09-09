
module Types.Check where

import qualified Syntax.Abstract as A
import Types.Monad
import Types.Equality
import Types.Metas

infer :: TermRep r => A.Expr -> TC r (Term r, Type r)
infer e = case e of

  A.Let d e -> checkDecl d $ infer e

  _ -> error $ "todo: infer " ++ show e

check :: TermRep r => A.Expr -> Type r -> TC r (Term r)
check e t = case A.elimView e of
  A.ElimV e els -> do
    (v, t') <- infer e
    checkElims v t' t els
  A.NoElim e    -> case e of

    A.Lam x e -> error "Lam"

    A.Let d e -> error "Let"

    A.Meta -> error "Meta"

    e | inferrable e -> do
      (v, t') <- infer e
      blockTerm v t (eqType t t')

    A.App{}   -> error "impossible: check A.App{}"
    A.Var{}   -> error "impossible: check A.Var{}"
    A.Prim{}  -> error "impossible: check A.Prim{}"
    A.Pi{}    -> error "Pi"
    A.Sigma{} -> error "Sigma"

-- | Check that something is a type
isType :: TermRep r => A.Expr -> TC r (Type r)
isType e = error "todo: isType"

-- | Check a declaration.
checkDecl :: TermRep r => A.Decl -> TC r a -> TC r a
checkDecl d k = case d of
  A.Ax x e -> do
    t <- isType e
    extendContext (TypedVar x t) k

  A.Def x et ev -> do
    t <- isType et
    v <- check ev t
    extendContext (DefinedVar x t v) k

-- | checkElims headValue headType targetType elims
checkElims :: TermRep r => Term r -> Type r -> Type r -> [A.Elim] -> TC r (Term r)
checkElims hd hdTy tgtTy els = error "todo: checkElims"

inferrable e = case e of
  A.Var{}   -> True
  A.Prim{}  -> True
  A.Pi{}    -> True
  A.Sigma{} -> True
  A.Lam{}   -> False
  A.Let _ e -> inferrable e
  A.Meta{}  -> False
  A.App e _ -> inferrable e

