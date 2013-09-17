{-# LANGUAGE RankNTypes, PatternGuards #-}
module Types.Check where

import Control.Applicative
import Control.Monad
import Data.Traversable hiding (mapM)
import Data.List

import IMPL.Term
import IMPL.Eval
import Types.Abs
import Types.Tel
import Types.Monad
import Types.Blocked
import qualified Syntax.Abstract as A
import Syntax.Abstract (Name)
import Syntax.Abstract.Pretty ()

import Debug

type StuckTC a = TC (Stuck a)

notStuck :: a -> StuckTC a
notStuck = return . NotStuck

stuckOn :: MetaVar -> StuckTC a -> StuckTC a
stuckOn x m = Stuck <$> newProblem x m

onStuck_ :: ProblemId a -> (a -> TC b) -> StuckTC b
onStuck_ pid f = Stuck <$> subProblem_ pid f

onStuck :: ProblemId a -> (a -> StuckTC b) -> StuckTC b
onStuck pid f = Stuck <$> subProblem pid f

bindStuck :: StuckTC a -> (a -> StuckTC b) -> StuckTC b
bindStuck m f = do
  r <- m
  case r of
    NotStuck x -> f x
    Stuck pid  -> onStuck pid f

checkProgram :: [A.Decl] -> TC ()
checkProgram = mapM_ checkDecl

checkDecl :: A.Decl -> TC ()
checkDecl d = atSrcLoc d $ do
  case d of
    A.TypeSig (A.Sig x t) -> checkTypeSig x t
    A.DataDef d xs cs     -> checkData d xs cs
    A.RecDef d xs c fs    -> checkRec d xs c fs
    A.FunDef f ps b       -> checkClause f ps b
  debug $ "Checked " ++ show d

checkTypeSig :: Name -> A.Expr -> TC ()
checkTypeSig x t = do
  set <- unview Set
  a <- check t set
  addConstant x a

withPars :: Type -> [Name]
         -> (Telescope -> [Term] -> Type -> TC a)
         -- ^ Note that the telescope lives in the original context,
         -- not the extended context.
         -> TC a
withPars a []       ret = ret EmptyTel [] a
withPars a (x : xs) ret = atSrcLoc x $ do
  v <- whnfView a
  case v of
    NotBlocked (Pi a b) ->
      extendContext x a       $ \x' ->
      withPars (absBody b) xs $ \tel vs c -> do
        v <- weakenBy (length xs) =<< unview (App (Var x') [])
        ret (a :> Abs (A.nameString x) tel) (v : vs) c
    _ -> typeError $ "Expected function type: " ++ show a

checkData :: Name -> [Name] -> [A.TypeSig] -> TC ()
checkData d xs cs = do
  a <- typeOf d
  withPars a xs $ \tel vs b -> do
    set <- unview Set
    equalType b set
    dvs <- unview $ App (Def d) (map Apply vs)
    mapM_ (checkConstr d dvs tel) cs

checkConstr :: Name -> Type -> Telescope -> A.TypeSig -> TC ()
checkConstr d dvs ptel (A.Sig c e) = atSrcLoc c $ do
  a        <- isType e
  (tel, b) <- telView a
  extendContextTel tel $ do
    dvs <- weakenBy (telSize tel) dvs
    whenStuck (equalType dvs b) $ \_ -> typeError $ show dvs ++ " != " ++ show b
  addConstructor c d ptel a

checkRec :: Name -> [Name] -> Name -> [A.TypeSig] -> TC ()
checkRec r xs c fs = do
  a <- typeOf r
  withPars a xs $ \ptel vs b -> do
    set <- unview Set
    equalType b set
    tel <- checkFields fs
    t <- unview (App (Def r) (map Apply vs))
    extendContext (A.name "_") t $ \self ->
      addProjections r ptel self t (zip (map A.typeSigName fs) [1..]) =<<
        weakenBy 1 tel
    addConstructor c r ptel (telPi tel t)

checkFields :: [A.TypeSig] -> TC Telescope
checkFields []               = return EmptyTel
checkFields (A.Sig f a : fs) = atSrcLoc f $ do
  a   <- isType a
  tel <- extendContext f a $ \_ -> checkFields fs
  return (a :> Abs (A.nameString f) tel)

addProjections :: Name -> Telescope -> Var -> Type ->
                  [(Name, Int)] -> Telescope -> TC ()
addProjections r ptel self t fs tel = case (fs, tel) of
  ([], EmptyTel)        -> return ()
  ((f, n) : fs, a :> b) -> do
    ta <- unview (Pi t (Abs "self" a))
    addProjection f n r ptel ta
    addProjections r ptel self t fs =<<
      absApply b =<< unview (App (Var self) [Proj n])
  (_, _) -> typeError "impossible.addProjections: lengths do not match"

checkClause :: Name -> [A.Pattern] -> A.Expr -> TC ()
checkClause f ps e = do
  a <- typeOf f
  checkPatterns ps a $ \ps _ b -> do
    v <- check e b
    addClause f ps v

checkPatterns :: [A.Pattern] -> Type -> ([Pattern] -> [Term] -> Type -> TC a) -> TC a
checkPatterns []       a ret = ret [] [] a
checkPatterns (p : ps) a ret = atSrcLoc p $ do
  av <- whnfView a
  case av of
    NotBlocked (Pi a b) ->
      checkPattern p a $ \p v -> do
        b <- weakenBy (bound p) b
        b <- absApply b v
        checkPatterns ps b $ \ps vs c -> do
          v <- weakenBy (bounds ps) v
          ret (p : ps) (v : vs) c
    _ -> typeError $ "Expected function type: " ++ show a
  where
    bounds = sum . map bound
    bound VarP        = 1
    bound (ConP c ps) = sum $ map bound ps

checkPattern :: A.Pattern -> Type -> (Pattern -> Term -> TC a) -> TC a
checkPattern p a ret = case p of
  A.VarP x  -> extendContext x a            $ \v -> ret VarP =<< unview (App (Var v) [])
  A.WildP _ -> extendContext (A.name "_") a $ \v -> ret VarP =<< unview (App (Var v) [])
  A.ConP c ps -> atSrcLoc c $ do
    def <- definitionOf c
    case def of
      Constructor _ d tel b -> do
        av <- whnfView a
        let isApply (Apply v) = Just v
            isApply Proj{}    = Nothing
        case ignoreBlocking av of
          App (Def d') es | d == d', Just vs <- mapM isApply es -> do
            b <- substs tel vs b
            checkPatterns ps b $ \ps args b -> do
              v <- unview (App (Con c) $ map Apply args)
              ret (ConP c ps) v
          _ -> typeError $ show c ++ " does not construct an element of " ++ show a

      _ -> typeError $ "Should be constructor: " ++ show c

isType :: A.Expr -> TC Type
isType e = do
  set <- unview Set
  check e set

check :: A.Expr -> Type -> TC Term
check e a = atSrcLoc e $ case e of
  A.App (A.Con c) es -> do
    def <- definitionOf c
    case def of
      Constructor _ d tel b -> do
        av <- whnfView a
        let isApply (Apply v) = Just v
            isApply Proj{}    = Nothing
        case ignoreBlocking av of
          App (Def d') els | d == d', Just vs <- mapM isApply els -> do
            b <- substs tel vs b
            r <- checkSpine es b
            case r of
              NotStuck (es, _) -> unview $ App (Con c) es
              Stuck pid        -> do
                x <- freshMeta a
                subProblem pid $ \(es, b) -> do
                  v <- unview $ App (Con c) es
                  equal a x v
                return x
          _ -> typeError $ "Constructor type error " ++ show e ++ " : " ++ show a
      _ -> typeError $ "Constructor type error " ++ show e ++ " : " ++ show a
  A.Meta l -> freshMeta a
  _ -> do
    r <- infer e
    case r of
      NotStuck (v, b) -> do
        r <- equalType a b
        case r of
          NotStuck () -> return v
          Stuck pid   -> do
            x <- freshMeta a
            subProblem pid $ \_ -> equal a x v
            return x
      Stuck pid -> do
        x <- freshMeta a
        subProblem pid $ \(v, b) -> do
          equalType a b `bindStuck` \_ -> equal a x v
        return x

infer :: A.Expr -> StuckTC (Term, Type)
infer e = atSrcLoc e $ case e of
  A.Set _ -> do
    set <- unview Set
    return $ NotStuck (set, set)
  A.Pi x a b -> do
    a   <- isType a
    b   <- extendContext x a $ \_ -> isType b
    v   <- unview $ Pi a (Abs (A.nameString x) b)
    set <- unview Set
    return $ NotStuck (v, set)
  A.Fun a b -> do
    a   <- isType a
    b   <- isType b
    v   <- unview . Pi a . Abs "_" =<< weakenBy 1 b
    set <- unview Set
    return $ NotStuck (v, set)
  A.App h es -> do
    (h, a) <- inferHead h
    r <- checkSpine es a
    let done (es, b) = do
          v <- unview (App h es)
          return (v, b)
    case r of
      NotStuck (es, b) -> NotStuck <$> done (es, b)
      Stuck pid        -> onStuck_ pid done
  _ -> typeError $ "todo infer\n  " ++ show e

inferHead :: A.Head -> TC (Head, Type)
inferHead h = atSrcLoc h $ case h of
  A.Var x -> do
    (n, a) <- lookupVar x
    return (Var n, a)
  A.Def x -> (,) (Def x) <$> typeOf x
  A.Con{} -> typeError $ "Cannot infer type of application of constructor " ++ show h

checkSpine :: [A.Elim] -> Type -> StuckTC ([Elim], Type)
checkSpine [] a = return $ NotStuck ([], a)
checkSpine (e:es) a = atSrcLoc e $ case e of
  A.Proj{} -> typeError $ "todo checkSpine " ++ show (e:es) ++ " : " ++ show a
  A.Apply e -> do
    a <- whnfView a
    case a of
      NotBlocked (Pi a b) -> do
        v <- check e a
        b <- absApply b v
        r <- checkSpine es b
        let ret (es, c) = return (Apply v : es, c)
        case r of
          NotStuck res -> NotStuck <$> ret res
          Stuck pid    -> onStuck_ pid ret
      NotBlocked a -> typeError $ "Expected function type " ++ show a ++ "\n  in application of " ++ show e
      Blocked x a -> stuckOn x (checkSpine (A.Apply e : es) =<< unview a)

equalType :: Type -> Type -> StuckTC ()
equalType a b = do
  set <- unview Set
  equal set a b

equal :: Type -> Term -> Term -> StuckTC ()
equal = checkEqual

checkEqual :: Type -> Term -> Term -> StuckTC ()
checkEqual a u v | u == v = return (NotStuck ())
checkEqual a u v = do
  av <- whnfView a
  case av of
    Blocked x _ -> stuckOn x (equal a u v)
    NotBlocked (Pi a b) ->
      underAbstraction a b $ \x b -> do
        x <- unview $ App (Var x) []
        u <- elim u [Apply x]
        v <- elim v [Apply x]
        equal b u v
    _ -> inferEqual u v

inferEqual :: Term -> Term -> StuckTC ()
inferEqual u v = do
  uu <- whnfView u
  vv <- whnfView v
  case (uu, vv) of
    (Blocked x _, _) -> stuckOn x (inferEqual u v)
    (_, Blocked x _) -> stuckOn x (inferEqual u v)
    (NotBlocked uu, NotBlocked vv) -> case (uu, vv) of
      (App (Meta x) es, v) -> metaAssign x es =<< unview v
      (u, App (Meta x) es) -> metaAssign x es =<< unview u
      (App h1 es1, App h2 es2) | h1 == h2 -> do
        a <- typeOfHead h1
        equalSpine a es1 es2
      _ -> typeError $ show uu ++ " != " ++ show vv

equalSpine :: Type -> [Elim] -> [Elim] -> StuckTC ()
equalSpine a [] [] = return $ NotStuck ()
equalSpine a (Apply u : es1) (Apply v : es2) = do
  av <- whnfView a
  case av of
    NotBlocked (Pi a b) -> do
      r <- checkEqual a u v
      let continue = do
            b <- absApply b u
            equalSpine b es1 es1
      case r of
        NotStuck () -> continue
        Stuck pid   -> onStuck pid $ \_ -> continue
    NotBlocked a -> typeError $ "impossible.equalSpine: expected function type " ++ show a
    Blocked x _  -> stuckOn x (equalSpine a (Apply u : es1) (Apply v : es2))
equalSpine a (Proj i : es1) (Proj j : es2) | i == j = typeError "todo: equalSpine proj"
equalSpine a es1 es2 = typeError $ show es1 ++ " != " ++ show es2 ++ " : " ++ show a

metaAssign :: MetaVar -> [Elim] -> Term -> StuckTC ()
metaAssign x es v = do
  mxs <- distinctVariables es
  case mxs of
    Nothing -> stuckOn x $ do
      u <- unview $ App (Meta x) es
      inferEqual u v
    Just xs -> do
      occursCheck xs v
      v <- lambdaAbstract xs v
      instantiateMeta x v
      notStuck ()

distinctVariables :: [Elim] -> TC (Maybe [Var])
distinctVariables es = do
  mxs <- traverse id <$> mapM isVar es
  return $ do
    xs <- mxs
    unless (nub xs == xs) Nothing
    return xs
  where
    isVar (Apply v) = isVarV <$> view v
    isVar Proj{}    = return Nothing

    isVarV (App (Var x) []) = Just x
    isVarV _                = Nothing

-- TODO: pruning
occursCheck :: [Var] -> Term -> TC ()
occursCheck xs v = occurs xs v

class Occurs a where
  occurs :: [Var] -> a -> TC ()

instance Occurs a => Occurs [a] where
  occurs xs = mapM_ (occurs xs)

instance (Occurs a, Occurs b) => Occurs (a, b) where
  occurs xs (x, y) = occurs xs x >> occurs xs y

instance Occurs a => Occurs (Abs a) where
  occurs xs b = do
    xs <- weakenBy 1 xs
    occurs xs (absBody b)

instance Occurs Term where
  occurs xs v = occurs xs =<< view v

instance Occurs TermView where
  occurs xs v = case v of
    App (Var x) es | notElem x xs -> typeError "occurs check failed"
    App h es                      -> occurs xs es
    Pi a b                        -> occurs xs (a, b)
    Lam b                         -> occurs xs b
    Equal a x y                   -> occurs xs (a, (x, y))
    Set                           -> return ()


instance Occurs Elim where
  occurs xs (Apply v) = occurs xs v
  occurs xs Proj{}    = return ()
