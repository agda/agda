
module Monad where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

import Name
import Term

data TCState = TCSt { stFresh     :: Integer
                    , stSignature :: [(Name, Term)]
                    }

initState = TCSt { stFresh = 0
                 , stSignature = []
                 }

data TCEnv = TCEnv { envSubst :: Env }

initEnv = TCEnv { envSubst = [] }

type TC = StateT TCState (ReaderT TCEnv (Either String))

runTC :: TC a -> Either String a
runTC m = runReaderT (evalStateT m initState) initEnv

fresh :: String -> TC Name
fresh x = do
  s <- get
  put s { stFresh = stFresh s + 1 }
  return $ Name x (stFresh s)

bindVar :: String -> (Name -> TC a) -> TC a
bindVar x ret = do
  x <- fresh x
  local (\e -> e { envSubst = (x, Var x []) : envSubst e }) (ret x)

addDecl :: Name -> Term -> TC ()
addDecl x v =
  modify $ \s -> s { stSignature = (x, v) : stSignature s }

addConst :: String -> TC Name
addConst x = do
  x <- fresh x
  addDecl x (Con x [])
  return x

addDef :: String -> Term -> TC Name
addDef x v = do
  x <- fresh x
  addDecl x v
  return x

resolveName :: String -> TC Term
resolveName s = do
  env <- asks envSubst
  sig <- gets stSignature
  case find var env ++ find con sig of
    []  -> fail $ "unbound name: " ++ s
    x:_ -> return x

  where
    find f sub = [ f x | x@(Name s' _) <- map fst sub, s == s' ]
    var x = Var x []
    con c = Con c []

varValue :: Name -> TC Term
varValue x = do
  env <- asks envSubst
  case lookup x env of
    Just v  -> return v
    Nothing -> fail $ "panic: unbound var " ++ show x

conValue :: Name -> TC Term
conValue c = do
  sig <- gets stSignature
  case lookup c sig of
    Just v  -> return v
    Nothing -> fail $ "panic: unbound con " ++ show c

getSubst :: TC Env
getSubst = asks envSubst

withSubst :: Env -> TC a -> TC a
withSubst sub = local $ \e -> e { envSubst = sub }
