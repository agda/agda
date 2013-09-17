{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, BangPatterns #-}
module Implementation.Simple.Monad where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Data.Map (Map)
import qualified Data.Map as Map

import Syntax.Abstract (name, nameString, Name, SrcLoc, noSrcLoc, HasSrcLoc(..))
import Types.Abs
import Types.Tel

import Implementation.Simple.Term

-- Monad ------------------------------------------------------------------

newtype TC a = TC { unTC :: ReaderT TCEnv (ErrorT TCErr (State TCState)) a }
  deriving (Functor, Applicative, Monad, MonadReader TCEnv, MonadState TCState, MonadError TCErr)

newtype Eval a = Eval { unEval :: TC a }
  deriving (Functor, Applicative, Monad, MonadReader TCEnv, MonadState TCState, MonadError TCErr)

runTC :: TC a -> IO (Either TCErr a)
runTC m = return $ flip evalState initState
                 $ runErrorT
                 $ flip runReaderT initEnv
                 $ unTC m

-- Env --------------------------------------------------------------------

data TCEnv = TCEnv
  { context       :: [(Name, Type)]
  , currentSrcLoc :: SrcLoc
  }

initEnv :: TCEnv
initEnv = TCEnv
  { context       = []
  , currentSrcLoc = noSrcLoc
  }

-- State ------------------------------------------------------------------

data TCState = TCState
  { signature :: Map Name Definition
  , metaStore :: Map MetaVar MetaInst
  }

initState :: TCState
initState = TCState
  { signature = Map.empty
  , metaStore = Map.empty
  }

data Definition = Constant Name Type
                | Constructor Name Name Telescope Type
                | Function Name Type [Clause]

data MetaInst = Open Type
              | Inst Type Term

-- Error ------------------------------------------------------------------

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) = show p ++ ": " ++ s

typeError :: String -> TC b
typeError err = do
  loc <- asks currentSrcLoc
  throwError $ TCErr loc err

-- Functions --------------------------------------------------------------

atSrcLoc :: HasSrcLoc a => a -> TC b -> TC b
atSrcLoc x = local $ \env -> env { currentSrcLoc = srcLoc x }

class (Applicative m, Monad m) => MonadEval m where
  eval :: Eval a -> m a

instance MonadEval Eval where
  eval = id

instance MonadEval TC where
  eval = unEval

view :: MonadEval m => Term -> m TermView
view = return . termView

unview :: MonadEval m => TermView -> m Term
unview = return . Term

addDefinition :: Name -> Definition -> TC ()
addDefinition x def = modify $ \s -> s { signature = Map.insert x def $ signature s }

addConstant :: Name -> Type -> TC ()
addConstant x a = addDefinition x (Constant x a)

addConstructor :: Name -> Name -> Telescope -> Type -> TC ()
addConstructor c d tel a = addDefinition c (Constructor c d tel a)

addClause :: Name -> [Pattern] -> Term -> TC ()
addClause f ps v = do
  Just def <- gets $ Map.lookup f . signature
  let ext (Constant x a)    = Function x a [c]
      ext (Function x a cs) = Function x a (cs ++ [c])
      ext Constructor{}     = error $ "impossible: addClause constructor"
  addDefinition f (ext def)
  where
    c = Clause ps v

nextMetaVar :: TC MetaVar
nextMetaVar = do
  m <- gets $ Map.maxViewWithKey . metaStore
  return $ case m of
    Nothing                  -> MetaId 0
    Just ((MetaId i, _), _) -> MetaId (i + 1)

contextTel :: TC Telescope
contextTel = foldr ext EmptyTel . reverse <$> asks context
  where
    ext (x, a) tel = a :> Abs (nameString x) tel

contextArgs :: TC [Term]
contextArgs = do
  n <- asks $ length . context
  return [ Term (App (Var i) []) | i <- [n - 1, n - 2..0] ]

freshMeta :: Type -> TC Term
freshMeta a = do
  tel   <- contextTel
  x     <- nextMetaVar
  modify $ \s -> s { metaStore = Map.insert x (Open $ telPi tel a) $ metaStore s }
  args  <- contextArgs
  return $ Term $ App (Meta x) $ map Apply args

extendContext :: Name -> Type -> (Var -> TC a) -> TC a
extendContext x a ret = local (\env -> env { context = (x, a) : context env }) (ret 0)

lookupVar :: Name -> TC (Var, Type)
lookupVar x = atSrcLoc x $ do
  cxt <- asks context
  case find 0 x cxt of
    Just (n, a) -> return (n, weakenBy' (n + 1) a)
    Nothing     -> typeError $ "impossible: not in scope " ++ show x
  where
    find _ x [] = Nothing
    find !i x ((y, a):cxt)
      | x == y = Just (i, a)
      | otherwise = find (i + 1) x cxt

definitionOf :: Name -> TC Definition
definitionOf x = atSrcLoc x $ do
  sig <- gets signature
  case Map.lookup x sig of
    Just d  -> return d
    Nothing -> typeError $ "impossible: Not in scope " ++ show x
  
typeOf :: Name -> TC Type
typeOf x = defType <$> definitionOf x
  where
    defType (Constant _ a)          = a
    defType (Constructor _ _ tel a) = telPi tel a
    defType (Function _ a _)        = a

underAbstraction :: Type -> Abs a -> (Var -> a -> TC b) -> TC b
underAbstraction a b ret = extendContext (name $ absName b) a $ \x -> ret x (absBody b)

telPi :: Telescope -> Type -> Type
telPi EmptyTel   a = a
telPi (a :> tel) b = Term $ Pi a $ fmap (`telPi` b) tel

-- DeBruijn trickery ------------------------------------------------------

weakenBy :: (Weaken a, MonadEval m) => Int -> a -> m a
weakenBy 0 x = return x
weakenBy n x = return $ weakenBy' n x

weaken :: Weaken a => a -> a
weaken = weakenBy' 1

weakenBy' :: Weaken a => Int -> a -> a
weakenBy' = weakenFromBy 0

class Weaken a where
  weakenFromBy :: Int -> Int -> a -> a

instance Weaken Head where
  weakenFromBy n k h = case h of
    Var i | i < n     -> h
          | otherwise -> Var (i + k)
    Con{}  -> h
    Def{}  -> h
    Meta{} -> h

instance Weaken Term where
  weakenFromBy n k (Term v) = Term (weakenFromBy n k v)

instance Weaken TermView where
  weakenFromBy n k v = case v of
    Lam b       -> Lam $ wk b
    Pi a b      -> Pi (wk a) (wk b)
    Equal a x y -> Equal (wk a) (wk x) (wk y)
    App h es    -> App (wk h) (wk es)
    Set         -> v
    where
      wk :: Weaken a => a -> a
      wk = weakenFromBy n k

instance Weaken a => Weaken [a] where
  weakenFromBy n k = map (weakenFromBy n k)

instance Weaken a => Weaken (Abs a) where
  weakenFromBy n k (Abs x b) = Abs x $ weakenFromBy (n + 1) k b

instance Weaken Elim where
  weakenFromBy n k e = case e of
    Apply e -> Apply (weakenFromBy n k e)
    Proj{}  -> e

substTel :: MonadEval m => Telescope -> [Term] -> Term -> m Term
substTel _ us v = return $ substs us v

substs []       v = v
substs (u : us) v = subst 0 u $ substs us v

absApply :: MonadEval m => Abs Term -> Term -> m Term
absApply a v = return $ absApply' a v

absApply' :: Abs Term -> Term -> Term
absApply' (Abs _ v) u = subst 0 u v

elim :: Term -> [Elim] -> Term
elim v [] = v
elim v es = elimV (termView v) es

elimV :: TermView -> [Elim] -> Term
elimV (App (Con c) es0) (Proj i : es1)
  | i >= length es0 = error $ "Bad elim: " ++ show (App (Con c) es0) ++ " " ++ show (Proj i)
  | otherwise       = elim v es1
  where Apply v = es0 !! i
elimV (App h es0) es1 = Term $ App h (es0 ++ es1)
elimV (Lam b) (Apply e : es) = elim (absApply' b e) es
elimV v es = error $ "Bad elim: " ++ show v ++ " " ++ show es


class Subst a where
  subst :: Int -> Term -> a -> a

instance Subst Term where
  subst n u (Term v) = Term (subst n u v)

instance Subst TermView where
  subst n u v = case v of
    App (Var i) es
      | i == n  -> termView $ u `elim` es
      | i > n   -> App (Var (i - 1)) (sub es)
    App h es    -> App h (sub es)
    Lam b       -> Lam $ sub b
    Pi a b      -> Pi (sub a) (sub b)
    Equal a x y -> Equal (sub a) (sub x) (sub y)
    Set         -> v
    where
      sub :: Subst a => a -> a
      sub = subst n u

instance Subst a => Subst [a] where
  subst n u = map (subst n u)

instance Subst a => Subst (Abs a) where
  subst n u (Abs x b) = Abs x $ subst (n + 1) (weaken u) b

instance Subst Elim where
  subst n u e = case e of
    Apply e -> Apply (subst n u e)
    Proj{}  -> e
