{-# LANGUAGE DeriveFunctor #-}

module Implementation.Simple.Eval where

import Control.Applicative
import Types.Blocked
import Implementation.Simple.Term
import Implementation.Simple.Monad

whnf :: Term -> TC (Blocked Term)
whnf (Term v) = case v of
  App (Meta x) es -> do
    i <- getMetaInst x
    case i of
      Open{}   -> return $ NotBlocked (Term v)
      Inst _ v -> whnf $ elim' v es
  App (Def f) es -> do
    def <- definitionOf f
    case def of
      Function _ _ cs -> whnfFun (Term v) es cs
      _               -> return $ NotBlocked (Term v)
  _ -> return $ NotBlocked (Term v)

whnfFun :: Term -> [Elim] -> [Clause] -> TC (Blocked Term)
whnfFun v _  []                    = return $ NotBlocked v
whnfFun v es (Clause ps body : cs) = do
  m <- match es ps body
  case m of
    Yes body    -> whnf body
    BlockedOn i -> return (Blocked i v)
    No          -> whnfFun v es cs

data Match a = Yes a
             | BlockedOn MetaVar
             | No
  deriving Functor

match :: [Elim] -> [Pattern] -> Term -> TC (Match Term)
match us             []          body = return $ Yes (elim' body us)
match (Apply u : es) (VarP : ps) body =
  fmap (subst 0 u) <$> match es ps body
match (Apply u : es) (ConP c cps : ps) body = do
  u <- whnf u
  case u of
    NotBlocked (Term (App (Con c') es'))
      | c' == c -> match (es' ++ es) (cps ++ ps) body
      | c' /= c -> return No
    Blocked i _ -> return (BlockedOn i)
    _           -> return No
match _ _ _ = return No
