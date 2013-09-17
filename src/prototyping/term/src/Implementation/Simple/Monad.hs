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
import Debug

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

data Definition = Constant Name ConstantKind Type
                | Constructor Name Name Telescope Type
                  -- ^ Constructor name, data type name, parameter
                  -- telescope, remaining type.
                | Projection Name Int Name Telescope Type
                  -- ^ Projection name, field number, record type
                  -- name, parameter telescope, remaining type.
                | Function Name Type [Clause]
  deriving Show

data ConstantKind = Postulate | Data | Record
  deriving Show

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

addConstant :: Name -> ConstantKind -> Type -> TC ()
addConstant x k a = addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> Telescope -> Type -> TC ()
addConstructor c d tel a = addDefinition c (Constructor c d tel a)

addProjection :: Name -> Int -> Name -> Telescope -> Type -> TC ()
addProjection f n r tel a = addDefinition f (Projection f n r tel a)

addClause :: Name -> [Pattern] -> Term -> TC ()
addClause f ps v = do
  Just def <- gets $ Map.lookup f . signature
  let ext (Constant x Postulate a) = Function x a [c]
      ext (Function x a cs)        = Function x a (cs ++ [c])
      ext (Constant _ k _)         = error $ "impossible: addClause " ++ show k
      ext Constructor{}            = error $ "impossible: addClause constructor"
      ext Projection{}             = error $ "impossible: addClause projection"
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

instantiateMeta :: MetaVar -> Term -> TC ()
instantiateMeta x v = do
  Open a <- getMetaInst x
  modify $ \s -> s { metaStore = Map.insert x (Inst a v) (metaStore s) }

getMetaInst :: MetaVar -> TC MetaInst
getMetaInst x = do
  Just i <- gets $ Map.lookup x . metaStore
  return i

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
    defType (Constant _ _ a)         = a
    defType (Constructor _ _ tel a)  = telPi tel a
    defType (Projection _ _ _ tel a) = telPi tel a
    defType (Function _ a _)         = a

typeOfMeta :: MetaVar -> TC Type
typeOfMeta x = do
  Just i <- gets $ Map.lookup x . metaStore
  return $ case i of
    Open a   -> a
    Inst a _ -> a

bang :: Show a => Int -> [a] -> a
bang n xs | length xs <= n = error $ "bang " ++ show n ++ " " ++ show xs
bang n xs = xs !! n

typeOfHead :: Head -> TC Type
typeOfHead (Var x) = asks $ weakenBy' (x + 1) . snd . bang x . context
typeOfHead (Def x) = typeOf x
typeOfHead (Con x) = typeOf x
typeOfHead (Meta x) = typeOfMeta x

underAbstraction :: Type -> Abs a -> (Var -> a -> TC b) -> TC b
underAbstraction a b ret = extendContext (name $ absName b) a $ \x -> ret x (absBody b)

telPi :: Telescope -> Type -> Type
telPi EmptyTel   a = a
telPi (a :> tel) b = Term $ Pi a $ fmap (`telPi` b) tel

-- Creates a term in the same context as the original term but lambda
-- abstracted over the given variables.q
lambdaAbstract :: MonadEval m => [Var] -> Term -> m Term
lambdaAbstract xs v = return $ lambda xs v

lambda :: [Var] -> Term -> Term
lambda []     v = v
lambda (x:xs) v = Term $ Lam $ Abs "_"
                $ weakenFromBy (x + 1) 1
                $ subst (x + 1) (Term $ App (Var 0) [])
                $ weaken $ lambda xs v

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

instance Weaken Var where
  weakenFromBy n k i | i < n     = i
                     | otherwise = i + k

instance Weaken Head where
  weakenFromBy n k h = case h of
    Var i  -> Var $ weakenFromBy n k i
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

instance Weaken Telescope where
  weakenFromBy n k tel = case tel of
    EmptyTel -> EmptyTel
    a :> b   -> weakenFromBy n k a :> weakenFromBy n k b

elim :: MonadEval m => Term -> [Elim] -> m Term
elim v es = return $ elim' v es

elim' :: Term -> [Elim] -> Term
elim' v [] = v
elim' v es = elimV (termView v) es

elimV :: TermView -> [Elim] -> Term
elimV (App (Con c) es0) (Proj i : es1)
  | i >= length es0 = error $ "Bad elim: " ++ show (App (Con c) es0) ++ " " ++ show (Proj i)
  | otherwise       = elim' v es1
  where Apply v = es0 !! i
elimV (App h es0) es1 = Term $ App h (es0 ++ es1)
elimV (Lam b) (Apply e : es) = elim' (absApply' b e) es
elimV v es = error $ "Bad elim: " ++ show v ++ " " ++ show es

class Subst a where
  -- | Variable zero is replaced by the /first/ element in the list.
  substs' :: [Term] -> a -> a

-- | Variable zero is replaced by the /last/ element in the list.
substs :: (MonadEval m, Subst a) => Telescope -> [Term] -> a -> m a
substs tel us v = return $ substs' (reverse us) v

subst :: Subst a => Int -> Term -> a -> a
subst n u = substs' (vars [0 .. n-1] ++ [u] ++ vars [n ..])
  where
  vars = map (\x -> Term (App (Var x) []))

absApply :: (MonadEval m, Subst a) => Abs a -> Term -> m a
absApply a t = return $ absApply' a t

absApply' :: Subst a => Abs a -> Term -> a
absApply' (Abs _ a) t = subst 0 t a

instance Subst Term where
  substs' us (Term v) = Term (substs' us v)

instance Subst TermView where
  substs' us v = case v of
    App (Var i) es -> termView $ (us !! i) `elim'` sub es
    App h es       -> App h (sub es)
    Lam b          -> Lam $ sub b
    Pi a b         -> Pi (sub a) (sub b)
    Equal a x y    -> Equal (sub a) (sub x) (sub y)
    Set            -> v
    where
      sub :: Subst a => a -> a
      sub = substs' us

instance Subst a => Subst [a] where
  substs' us = map (substs' us)

instance Subst a => Subst (Abs a) where
  substs' us (Abs x b) =
    Abs x $ substs' (Term (App (Var 0) []) : map weaken us) b

instance Subst Elim where
  substs' us e = case e of
    Apply e -> Apply (substs' us e)
    Proj{}  -> e

instance Subst Telescope where
  substs' us EmptyTel = EmptyTel
  substs' us (a :> b) = substs' us a :> substs' us b
