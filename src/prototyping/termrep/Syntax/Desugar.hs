{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, OverlappingInstances #-}

module Syntax.Desugar where

import Control.Arrow ((***))
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function
import Data.List

import qualified Syntax.Abs as C
import Syntax.Abstract

type Ctx   = [(Name, Scheme)]
type Scope = ReaderT Ctx (Either String)

data ArgCount = Implicit Int | Explicit Int
type Scheme = [ArgCount]

runScope :: Scope a -> Either String a
runScope m = runReaderT m []

primitives' :: [Name]
primitives' =
  [ "Set", "Zero", "One", "Two", "tt", "true", "false", "absurd", "if", "fst", "snd", "pair" ]

primScheme "fst"    = [Explicit 1]
primScheme "snd"    = [Explicit 1]
primScheme "pair"   = [Explicit 2]
primScheme "absurd" = [Implicit 1]
primScheme _        = []

primitives = [ (x, primScheme x) | x <- primitives' ]

type CPS r a = (a -> r) -> r

sequenceCPS :: [CPS r a] -> CPS r [a]
sequenceCPS []       ret = ret []
sequenceCPS (m : ms) ret =
  m $ \x -> sequenceCPS ms $ \xs -> ret (x : xs)

thread :: (a -> CPS r b) -> [a] -> CPS r [b]
thread f = sequenceCPS . map f

newName :: C.Ident -> Scope Name
newName (C.Ident x)
  | notElem x primitives' = return x
  | otherwise             = fail $ x ++ " is a reserved identifier"

oldName :: C.Ident -> Scope (Expr, Scheme)
oldName (C.Ident x) =
  case lookup x primitives of
    Just s -> return (Prim x, s)
    Nothing -> do
      r <- asks $ lookup x
      case r of
        Just n  -> return (Var x, n)
        Nothing -> fail $ "Unbound name '" ++ x ++ "'"

bindName :: Name -> Scheme -> Scope a -> Scope a
bindName x s = local ((x, s):)

appV :: C.Expr -> [C.Expr]
appV (C.App e1 e2) = appV e1 ++ [e2]
appV e = [e]

lambdaBind :: C.Expr -> CPS (Scope a) [Name]
lambdaBind e ret = thread lambdaVar (appV e) ret
  where
    lambdaVar C.Meta ret = ret "_"
    lambdaVar (C.Var x) ret = do
      x <- newName x
      bindName x [] $ ret x
    lambdaVar e ret = fail $ "expected bound names, found " ++ show e

checkProg :: C.Program -> Scope Expr
checkProg (C.Prog ds) =
  thread checkDecl (list ds) $ \ds -> return $ foldr Let (Prim "tt") ds
  where
    list (C.Cons x xs) = x : list xs
    list (C.Unit x) = [x]

checkDecl :: C.Decl -> CPS (Scope a) Decl
checkDecl (C.Ax x a) ret = do
  x      <- newName x
  (a, n) <- checkScheme a
  bindName x n $ ret $ Ax x a
checkDecl (C.Def x a e) ret = do
  x      <- newName x
  (a, n) <- checkScheme a
  e      <- checkExpr e
  bindName x n $ ret $ Def x a e

checkScheme :: C.Expr -> Scope (Type, Scheme)
checkScheme (C.ImpPi xs a b) = do
  a <- checkExpr a
  lambdaBind xs $ \xs -> do
    (b, s) <- checkScheme b
    return (foldr (flip Pi a) b xs, implicit (length xs) s)
checkScheme (C.Pi xs a b) = do
  a <- checkExpr a
  lambdaBind xs $ \xs -> do
    (b, s) <- checkScheme b
    return (foldr (flip Pi a) b xs, explicit (length xs) s)
checkScheme a = do
  a <- checkExpr a
  return (a, [])

implicit :: Int -> Scheme -> Scheme
implicit n (Implicit m : s) = Implicit (n + m) : s
implicit n s                = Implicit n : s

explicit :: Int -> Scheme -> Scheme
explicit n (Explicit m : s) = Explicit (n + m) : s
explicit n []               = []
explicit n s                = Explicit n : s

checkExpr :: C.Expr -> Scope Expr
checkExpr e = case e of
  C.Lam xs e     -> lambdaBind xs $ \xs -> flip (foldr Lam) xs <$> checkExpr e
  C.Pi xs a b    -> do
    a <- checkExpr a
    lambdaBind xs $ \xs -> do
      b <- checkExpr b
      return $ foldr (flip Pi a) b xs
  C.Sigma xs a b -> do
    a <- checkExpr a
    lambdaBind xs $ \xs -> do
      b <- checkExpr b
      return $ foldr (flip Sigma a) b xs
  C.Let ds e     ->
    thread checkDecl ds $ \ds -> flip (foldr Let) ds <$> checkExpr e
  C.Fun a b      -> Pi "_" <$> checkExpr a <*> checkExpr b
  C.Meta         -> return Meta
  C.Paren e      -> checkExpr e
  _ -> case appView e of
    (C.Var x, es) -> do
      (x, s) <- oldName x
      es     <- mapM checkExpr es
      return $ expandImplicit s [] x es
    (e, es) -> foldl App <$> checkExpr e <*> mapM checkExpr es

appView :: C.Expr -> (C.Expr, [C.Expr])
appView (C.App e1 e2) = id *** (++ [e2]) $ appView e1
appView (C.Paren e) = appView e
appView e = (e, [])

expandImplicit :: Scheme -> [Name] -> Expr -> [Expr] -> Expr
expandImplicit (Implicit n : s) xs e es =
  expandImplicit s xs (app e $ replicate n Meta) es
expandImplicit [] xs e es = lam xs $ app e es
expandImplicit (Explicit n : s) xs e es
  | m >= n    = expandImplicit s xs (app e es1) es2
  | otherwise = expandImplicit s (xs ++ ys) (app e $ es ++ map Var ys) []
    where
      (es1, es2) = splitAt n es
      m          = length es
      ys         = freshN (n - m) (e, es)

lam xs e = foldr Lam e xs
app e es = foldl App e es

class Names a where
  names :: a -> Set Name

instance Names Name where
  names = Set.singleton

instance Names a => Names [a] where
  names = Set.unions . map names

instance (Names a, Names b) => Names (a, b) where
  names (x, y) = Set.union (names x) (names y)

instance Names Decl where
  names (Def x a e) = Set.insert x $ (Set.union `on` names) a e
  names (Ax x a)    = Set.insert x $ names a

instance Names Expr where
  names e = case e of
    Lam x e     -> names (x, e)
    Pi x a b    -> names (x, (a, b))
    Sigma x a b -> names (x, (a, b))
    Let ds e    -> names (ds, e)
    Meta        -> Set.empty
    App a b     -> names (a, b)
    Var x       -> names x
    Prim{}      -> Set.empty

freshN :: Names a => Int -> a -> [Name]
freshN n e = take n (allNames \\ Set.toList (names e))
  where
    allNames = [ s ++ [c] | s <- "" : allNames, c <- ['a'..'z'] ]
