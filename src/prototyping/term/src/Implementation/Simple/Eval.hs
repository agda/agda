{-# LANGUAGE DeriveFunctor #-}

module Implementation.Simple.Eval where

import Control.Applicative
import Control.Arrow ((***))
import Types.Blocked
import Implementation.Simple.Term
import Implementation.Simple.Monad

import Debug

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
  App J (_ : x : _ : _ : Apply p : Apply (Term (App Refl [])) : es) ->
    whnf $ elim' p (x : es)
  _ -> return $ NotBlocked (Term v)

whnfFun :: Term -> [Elim] -> [Clause] -> TC (Blocked Term)
whnfFun v _  []                    = return $ NotBlocked v
whnfFun v es (Clause ps body : cs) = do
  m <- match es ps body
  case m of
    BlockedOn i          -> return (Blocked i v)
    No                   -> whnfFun v es cs
    Yes (us, (body, es)) -> do
      body <- substs (error "todo: telescope") us body
      whnf (elim' body es)

data Match a = Yes a
             | BlockedOn MetaVar
             | No
  deriving (Show, Functor)

match :: [Elim] -> [Pattern] -> Term -> TC (Match ([Term], (Term, [Elim])))
match es             []                body = return $ Yes ([], (body, es))
match (Apply u : es) (VarP       : ps) body = fmap ((u :) *** id) <$>
                                                match es ps body
match (Apply u : es) (ConP c cps : ps) body = do
  u <- whnf u
  case u of
    NotBlocked (Term (App (Con c') es'))
      | c' == c -> match (es' ++ es) (cps ++ ps) body
      | c' /= c -> return No
    Blocked i _ -> return (BlockedOn i)
    _           -> return No
match _ _ _ = return No
