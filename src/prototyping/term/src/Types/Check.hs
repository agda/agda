{-# LANGUAGE RankNTypes, PatternGuards #-}
module Types.Check where

import Control.Applicative
import Data.Traversable hiding (mapM)

import IMPL.Term
import IMPL.Eval
import Types.Abs
import Types.Tel
import Types.Monad
import Types.Blocked
import qualified Syntax.Abstract as A
import Syntax.Abstract (Name)
import Syntax.Abstract.Pretty ()

import Debug.Trace

debug :: String -> TC ()
debug s = trace s $ return ()

checkProgram :: [A.Decl] -> TC ()
checkProgram = mapM_ checkDecl

checkDecl :: A.Decl -> TC ()
checkDecl d = atSrcLoc d $ do
  case d of
    A.TypeSig (A.Sig x t) -> checkTypeSig x t
    A.DataDef d xs cs     -> checkData d xs cs
    A.FunDef f ps b       -> checkClause f ps b
    _                     -> typeError $ "todo: checkDecl\n  " ++ show d
  debug $ "Checked " ++ show d

checkTypeSig :: Name -> A.Expr -> TC ()
checkTypeSig x t = do
  set <- unview Set
  a <- check t set
  addConstant x a

checkData :: Name -> [Name] -> [A.TypeSig] -> TC ()
checkData d xs cs = do
  a <- typeOf d
  withPars a xs $ \vs b -> do
    set <- unview Set
    equalType b set
    dvs <- unview $ App (Def d) (map Apply vs)
    mapM_ (checkConstr d dvs) cs
  where
    withPars a [] ret = ret [] a
    withPars a (x : xs) ret = atSrcLoc x $ do
      v <- whnfView a
      case v of
        NotBlocked (Pi a b) ->
          extendContext x a       $ \x ->
          withPars (absBody b) xs $ \vs c -> do
            v <- weakenBy (length xs) =<< unview (App (Var x) [])
            ret (v : vs) c
        _ -> typeError $ "Expected function type: " ++ show a

checkConstr :: Name -> Type -> A.TypeSig -> TC ()
checkConstr d dvs (A.Sig c e) = atSrcLoc c $ do
  a        <- isType e
  (tel, b) <- telView a
  extendContextTel tel $ do
    dvs <- weakenBy (telSize tel) dvs
    whenStuck (equalType dvs b) $ \_ -> typeError $ show dvs ++ " != " ++ show b
  addConstructor c d tel a

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
            b <- substTel tel vs b
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
            b <- substTel tel vs b
            r <- checkSpine es b
            case r of
              NotStuck (es, _) -> unview $ App (Con c) es
              Stuck pid        -> do
                x <- freshMeta a
                subProblem pid $ \(es, b) -> do
                  v <- unview $ App (Con c) es
                  () <$ equal a x v
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
            subProblem pid $ \_ -> () <$ equal a x v
            return x
      Stuck pid -> do
        x <- freshMeta a
        subProblem pid $ \(v, b) -> do
          r <- equalType a b
          case r of
            NotStuck () -> () <$ equal a x v
            Stuck pid   -> () <$ subProblem pid (\_ -> () <$ equal a x v)
        return x

infer :: A.Expr -> TC (Stuck (Term, Type))
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
      Stuck pid        -> Stuck <$> subProblem pid done
  _ -> typeError $ "todo infer\n  " ++ show e

inferHead :: A.Head -> TC (Head, Type)
inferHead h = atSrcLoc h $ case h of
  A.Var x -> do
    (n, a) <- lookupVar x
    return (Var n, a)
  A.Def x -> (,) (Def x) <$> typeOf x
  A.Con{} -> typeError $ "Cannot infer type of application of constructor " ++ show h

checkSpine :: [A.Elim] -> Type -> TC (Stuck ([Elim], Type))
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
          Stuck pid    -> Stuck <$> subProblem pid ret
      NotBlocked a -> typeError $ "Expected function type " ++ show a ++ "\n  in application of " ++ show e
      Blocked x a -> Stuck <$> newProblem x (checkSpine (A.Apply e : es) =<< unview a)

equalType :: Type -> Type -> TC (Stuck ())
equalType a b = do
  set <- unview Set
  equal set a b

equal :: Type -> Term -> Term -> TC (Stuck ())
equal a x y = case a of
  _ | x == y -> return $ NotStuck ()
  _ -> typeError $ show x ++ " != " ++ show y ++ " : " ++ show a

