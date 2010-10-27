{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module TypeChecker where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List

import qualified Lam.Abs as A
import Lam.Abs (Prog(..), Decl(..), VarName(..), Expr)
import Lam.Print
import Syntax
import Name
import Stack

instance Monad m => Applicative (ReaderT e m) where
  pure  = return
  (<*>) = ap

newtype TCM a = TCM { unTCM :: ReaderT Env (Either String) a }
  deriving (Functor, Applicative, Monad, MonadReader Env, MonadError String)

runTCM :: Env -> TCM a -> Either String a
runTCM env m = runReaderT (unTCM m) env

type Type = Term

data Defn = Ax Name Type
          | Df Name Type Term
  deriving Show

-- Environment ------------------------------------------------------------

data Env = Env { context :: Map VarName Defn }

emptyEnv = Env { context = Map.empty }

bindVar_ :: VarName -> Type -> (Name -> TCM a) -> TCM a
bindVar_ x a k = bindVar x y a (k y)
  where
    y = topLevelName x

bindVar :: VarName -> Name -> Type -> TCM a -> TCM a
bindVar x y a k =
  local (\env -> env { context = Map.insert x (Ax y a) $ context env }) k

bindDef :: VarName -> Type -> Term -> (Name -> TCM a) -> TCM a
bindDef x a v k =
    local (\env -> env { context = Map.insert x (Df y a v) $ context env }) (k y)
  where
    y = topLevelName x

-- TODO: Uniqueness
topLevelName :: VarName -> Name
topLevelName (VarName x) = nm x

checkProgram :: Prog -> TCM [Defn]
checkProgram (Prog ds) = checkDecls ds return

checkDecls :: [Decl] -> ([Defn] -> TCM a) -> TCM a
checkDecls [] ret = ret []
checkDecls (d : ds) ret =
  checkDecl d $ \d ->
  checkDecls ds $ \ds ->
  ret (d : ds)

checkDecl :: Decl -> (Defn -> TCM a) -> TCM a
checkDecl (Axiom x t) ret = do
  a <- isType t
  bindVar_ x a $ \x ->
    ret $ Ax x a
checkDecl (Def x t e) ret = do
  a <- isType t
  v <- check e a
  bindDef x a v $ \x ->
    ret $ Df x a v

lookupVar :: VarName -> TCM (Name, Type)
lookupVar x = do
  cxt <- asks context
  case Map.lookup x cxt of
    Just (Ax x a)   -> return (x, a)
    Just (Df x a _) -> return (x, a)
    Nothing         -> fail $ "Unbound variable: " ++ printTree x

isType :: Expr -> TCM Type
isType e = check e Set

infer :: Expr -> TCM (Term, Type)
infer e = case singleApp $ singlePi e of
  A.Var x    -> do
    (x, a) <- lookupVar x
    return $ (Free x, a)
  A.Fun s t  -> do
    a <- isType s
    b <- isType t
    let x = nm "Fun" <: "_"
    return ((x :<- a) --> b, Set)
  A.Pi [A.Bind [A.Var x] s] t -> do
    a <- isType s
    bindVar_ x a $ \x -> do
      b <- isType t
      return ((x :<- a) --> b, Set)
  A.Pi _ _ -> fail "bad Pi"
  A.Apps [f, e] -> do
    (u, a)       <- infer f
    let me = nm "infer-App" -- TODO
    (x :<- a, b) <- piView me (whnf a)
      `catchError` \_ -> fail $ "Not a pi: " ++ pretty (whnf a) ++ ", when inferring the type of " ++ printTree (A.Apps [f, e])
    v <- check e a
    return (App u v, substitute v x b)
  A.Apps _ -> fail "bad application"
  A.Star -> return (Set, Set)
  A.Lam _ _ -> fail "Cannot infer type of lambda"

singleLambda :: Expr -> Expr
singleLambda (A.Lam (x : xs) e)
  | not (null xs) = A.Lam [x] $ A.Lam xs e
singleLambda e = e

singlePi :: Expr -> Expr
singlePi (A.Pi (A.Bind (x : xs) s : bs) t) =
  A.Pi [A.Bind [x] s] $ mkPi (A.Bind xs s : bs) t
  where
    mkPi (A.Bind [] _ : bs) t = mkPi bs t
    mkPi [] t                 = t
    mkPi bs t                 = A.Pi bs t
singlePi e = e

singleApp :: Expr -> Expr
singleApp (A.Apps [e]) = singleApp e
singleApp (A.Apps (e1 : e2 : es))
  | not (null es) = singleApp (A.Apps (A.Apps [e1, e2] : es))
singleApp e = e

check :: Expr -> Type -> TCM Term
check e a =
  case singleLambda e of
    A.Lam [x] e -> do
      (y :<- a, b) <- piView (topLevelName x) (whnf a)
        `catchError` \_ -> fail $ "Not a pi: " ++ pretty (whnf a) ++ ", when checking " ++ printTree (A.Lam [x] e) ++ " : " ++ pretty a
      bindVar x y a $ do
        u <- check e b
        return $ lam y u
    A.Lam _ _ -> fail "impossible: bad lambda"
    _ -> do
      (v, b) <- infer e
      a === b
      return v

(===) :: Term -> Term -> TCM ()
u === v
  | u' == v'  = return ()
  | otherwise = fail $ show u' ++ " =/= " ++ show v'
  where
    u' = normalize u
    v' = normalize v

whnf :: Term -> Term
whnf v = case v of
  Free _  -> v
  Lam _   -> v
  Pi _ _  -> v
  Set     -> v
  App u v -> case whnf u of
    Lam b -> whnf (instantiate v b)
    u     -> App u v
  Bound _ -> error "impossible: whnf Bound"

normalize :: Term -> Term
normalize v = norm 0 v
  where
    norm i v = case whnf v of
      App u v -> App (norm i u) (norm i v)
      Lam b   -> Lam (normScope b)
      Pi a b  -> Pi (norm i a) (normScope b)
      v       -> v
      where
        normScope b = abstract x $ norm (i + 1) $ instantiate (Free x) b
        x = nm "norm" :< ("x", i)

nameToVarName :: Name -> VarName
nameToVarName x = VarName $ intercalate "." $ map f $ toList x
  where
    f (s, 0) = s
    f (s, n) = s ++ "_" ++ show n

pretty = printTree . toAbstract

toAbstract :: Term -> Expr
toAbstract v = case v of
  Free x -> A.Var $ nameToVarName x
  Bound _ -> error "impossible: toAbstract Bound"
  Set -> A.Star
  App u v -> apps [toAbstract u, toAbstract v]
    where
      apps (A.Apps us : vs) = apps (us ++ vs)
      apps us = A.Apps us
  Lam b -> mkLam [nameToVarName x] $ toAbstract $ instantiate (Free x) b
    where
      x = nm (varName b)
      mkLam xs (A.Lam ys e) = mkLam (xs ++ ys) e
      mkLam xs e = A.Lam xs e
  Pi a b
    | varName b == "_" ->
        A.Fun (toAbstract a) (toAbstract $ instantiate (Free x) b)
    | otherwise ->
        mkPi [A.Bind [A.Var $ nameToVarName x] $ toAbstract a] $
             toAbstract $ instantiate (Free x) b
    where
      x = nm (varName b)
      mkPi bs (A.Pi bs' e) = mkPi (bs ++ bs') e
      mkPi bs e = A.Pi (binds bs) e
      binds (A.Bind xs s : A.Bind ys t : bs)
        | s == t = binds (A.Bind (xs ++ ys) s : bs)
      binds (b : bs) = b : binds bs
      binds [] = []

toAbstractDecl :: Defn -> Decl
toAbstractDecl (Ax x a)   = Axiom (nameToVarName x) (toAbstract a)
toAbstractDecl (Df x a v) = Def (nameToVarName x) (toAbstract a) (toAbstract v)
