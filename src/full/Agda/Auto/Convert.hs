{-# LANGUAGE CPP #-}

module Agda.Auto.Convert where

import Agda.Utils.Impossible
#include "../undefined.h"

import Control.Applicative hiding (getConst, Const(..))
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Error

import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as I
import qualified Agda.Syntax.Common as C
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Position as SP
import qualified Agda.TypeChecking.Monad.Base as MB
import Agda.TypeChecking.Monad.Signature (getConstInfo, getDefFreeVars, getImportedSignature)
import Agda.Utils.Permutation (Permutation(Perm), idP, permute, takeP)
import Agda.Interaction.BasicOps (rewrite, Rewrite(..))
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base (mvJudgement, mvPermutation, getMetaInfo, ctxEntry, envContext, clEnv)
import Agda.TypeChecking.Monad.MetaVars (lookupMeta, withMetaInfo)
import Agda.TypeChecking.Monad.Context (getContextArgs)
import Agda.TypeChecking.Monad.Constraints (getAllConstraints)
import Agda.TypeChecking.Substitute (piApply, raise)
import qualified Agda.TypeChecking.Substitute as I (absBody)
import Agda.TypeChecking.Reduce (Normalise, normalise, instantiate)
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Free (freeIn)
import qualified Agda.Utils.HashMap as HMap

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

import Agda.Auto.CaseSplit hiding (lift)


norm :: Normalise t => t -> MB.TCM t
norm x = normalise x
--norm x = return x

type O = (Maybe Int, AN.QName) -- Nothing - Def, Just npar - Con with npar parameters which don't appear in Agda

data TMode = TMAll -- can be extended to distinguish between different modes (all, only def)
 deriving Eq

type MapS a b = (Map a b, [a])
initMapS = (Map.empty, [])
popMapS r w = do (m, xs) <- gets r
                 case xs of
                  [] -> return Nothing
                  (x:xs) -> do
                   modify (w (m, xs))
                   return $ Just x

data S = S {sConsts :: MapS AN.QName (TMode, ConstRef O),
            sMetas :: MapS I.MetaId (Metavar (Exp O) (RefInfo O), Maybe (MExp O, [MExp O]), [I.MetaId]),
            sEqs :: MapS Int (Maybe (Bool, MExp O, MExp O)),
            sCurMeta :: Maybe I.MetaId,
            sMainMeta :: I.MetaId
           }

type TOM = StateT S MB.TCM

tomy :: I.MetaId -> [(Bool, AN.QName)] -> [I.Type] -> MB.TCM ([ConstRef O], [MExp O], Map I.MetaId (Metavar (Exp O) (RefInfo O), MExp O, [MExp O], [I.MetaId]), [(Bool, MExp O, MExp O)], Map AN.QName (TMode, ConstRef O))
tomy imi icns typs = do
 eqs <- getEqs
 let
  r :: [AN.QName] -> TOM [AN.QName]
  r projfcns = do
   nxt <- popMapS sConsts (\x y -> y {sConsts = x})
   case nxt of
    Just cn -> do
     cmap <- fst `liftM` gets sConsts
     let (mode, c) = cmap Map.! cn
     def <- lift $ getConstInfo cn
     let typ = MB.defType def
         defn = MB.theDef def
     typ <- lift $ norm typ
     typ' <- tomyType typ
     let clausesToDef clauses = do
           clauses' <- tomyClauses clauses
           let narg = case clauses of
                        [] -> 0
                        I.Clause {I.clausePats = xs} : _ -> length xs
           return (Def narg clauses' Nothing Nothing, [])
     (cont, projfcns2) <- case defn of
      MB.Axiom {} -> return (Postulate, [])
      MB.Function {MB.funClauses = clauses} -> clausesToDef clauses
      MB.Primitive {MB.primClauses = Just clauses} -> clausesToDef clauses
      MB.Primitive {} -> throwError $ strMsg "Auto: Primitive functions are not supported"
      MB.Datatype {MB.dataCons = cons} -> do
       cons2 <- mapM (\con -> getConst True con TMAll) cons
       return (Datatype cons2 [], [])
      MB.Record {MB.recFields = fields, MB.recTel = tel} -> do -- the value of recPars seems unreliable or don't know what it signifies
       let pars n (I.El _ (I.Pi it typ)) = C.Arg (C.domInfo it) (I.var n) :
                                           pars (n - 1) (I.unAbs typ)
           pars n (I.El s (I.Shared p))  = pars n (I.El s (I.derefPtr p))
           pars _ (I.El _ _) = []
           contyp npar I.EmptyTel = I.El (I.mkType 0 {- arbitrary -}) (I.Def cn (pars (npar - 1) typ))
           contyp npar (I.ExtendTel it (I.Abs v tel)) = I.El (I.mkType 0 {- arbitrary -}) (I.Pi it (I.Abs v (contyp (npar + 1) tel)))
           contyp npar (I.ExtendTel it I.NoAbs{})     = __IMPOSSIBLE__
       contyp' <- tomyType $ contyp 0 tel
       cc <- lift $ liftIO $ readIORef c
       let Datatype [con] [] = cdcont cc
       lift $ liftIO $ modifyIORef con (\cdef -> cdef {cdtype = contyp'})

       projfcns <- mapM (\name -> getConst False name TMAll) (map C.unArg fields)

       return (Datatype [con] projfcns, []{-map snd fields-})
      MB.Constructor {MB.conData = dt} -> do
       _ <- getConst False dt TMAll -- make sure that datatype is included
       cc <- lift $ liftIO $ readIORef c
       let (Just nomi, _) = cdorigin cc
       return (Constructor (nomi - cddeffreevars cc), [])
     lift $ liftIO $ modifyIORef c (\cdef -> cdef {cdtype = typ', cdcont = cont})
     r $ projfcns2 ++ projfcns
    Nothing -> do
     nxt <- popMapS sMetas (\x y -> y {sMetas = x})
     case nxt of
      Just mi -> do
       mapM_ (\((_, e, i), eqi) -> do
         when (fmExp mi e || fmExp mi i) $ do
          (eqsm, eqsl) <- gets sEqs
          when (Map.notMember eqi eqsm) $ do
           modify $ \s -> s {sEqs = (Map.insert eqi Nothing eqsm, eqi : eqsl)}
        ) (zip eqs [0..])
       mv <- lift $ lookupMeta mi
       msol <- case MB.mvInstantiation mv of
                     MB.InstV{} ->
                      lift $ withMetaInfo (getMetaInfo mv) $ do
                       args <- getContextArgs
                       --sol <- norm (I.MetaV mi args)
                       sol <- instantiate (I.MetaV mi args)
                       return $ Just sol
                     _ -> return Nothing
       case msol of
        Nothing -> return ()
        Just sol -> do
         m <- getMeta mi
         sol' <- tomyExp sol
         modify $ \s -> s {sEqs = (Map.insert (Map.size (fst $ sEqs s)) (Just (False, Meta m, sol')) (fst $ sEqs s), snd $ sEqs s)}
       let tt = MB.jMetaType $ mvJudgement mv
           minfo = getMetaInfo mv
           localVars = map (snd . C.unDom . ctxEntry) . envContext . clEnv $ minfo
       (targettype, localVars) <- lift $ withMetaInfo minfo $ do
        vs <- getContextArgs
        let targettype = tt `piApply` permute (takeP (length vs) $ mvPermutation mv) vs
        targettype <- norm targettype
        localVars <- mapM norm localVars
        return (targettype, localVars)
       modify (\s -> s {sCurMeta = Just mi})
       typ' <- tomyType targettype
       ctx' <- mapM tomyType localVars
       modify (\s -> s {sCurMeta = Nothing})
       modify (\s -> s {sMetas = (Map.adjust (\(m, _, deps) -> (m, Just (typ', ctx'), deps)) mi (fst $ sMetas s), snd $ sMetas s)})
       r projfcns
      Nothing -> do
       nxt <- popMapS sEqs (\x y -> y {sEqs = x})
       case nxt of
        Just eqi -> do
         let (ineq, e, i) = eqs !! eqi
         e' <- tomyExp e
         i' <- tomyExp i
         modify (\s -> s {sEqs = (Map.adjust (\_ -> Just (ineq, e', i')) eqi (fst $ sEqs s), snd $ sEqs s)})
         r projfcns
        Nothing ->
         return projfcns
 ((icns', typs'), s) <- runStateT
  (do _ <- getMeta imi
      icns' <- mapM (\(iscon, name) -> getConst iscon name TMAll) icns
      typs' <- mapM tomyType typs
      projfcns <- r []
      projfcns' <- mapM (\name -> getConst False name TMAll) projfcns
      [] <- r []
      return (projfcns' ++ icns', typs')
  ) (S {sConsts = initMapS, sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing, sMainMeta = imi})
 lift $ liftIO $ mapM_ categorizedecl icns'
 return (icns', typs', Map.map flatten (fst (sMetas s)), map fromJust $ Map.elems (fst (sEqs s)), fst (sConsts s))
 where
 flatten (x, Just (y, z), w) = (x, y, z, w)
 flatten (x, Nothing, w) = __IMPOSSIBLE__

 fromJust (Just x) = x
 fromJust Nothing = __IMPOSSIBLE__

getConst :: Bool -> AN.QName -> TMode -> TOM (ConstRef O)
getConst iscon name mode = do
 def <- lift $ getConstInfo name
 case MB.theDef def of
  MB.Record {MB.recCon = conname} -> do
   cmap <- fst `liftM` gets sConsts
   case Map.lookup name cmap of
    Just (mode', c) ->
     if iscon then do
      cd <- lift $ liftIO $ readIORef c
      let Datatype [con] _ = cdcont cd
      return con
     else
      return c
    Nothing -> do
     mainm <- gets sMainMeta
     dfv <- lift $ getdfv mainm name
     let nomi = I.arity (MB.defType def)
     ccon <- lift $ liftIO $ newIORef (ConstDef {cdname = show name ++ ".CONS", cdorigin = (Just nomi, conname), cdtype = __IMPOSSIBLE__, cdcont = Constructor (nomi - dfv), cddeffreevars = dfv}) -- ?? correct value of deffreevars for records?
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = show name, cdorigin = (Nothing, name), cdtype = __IMPOSSIBLE__, cdcont = Datatype [ccon] [], cddeffreevars = dfv}) -- ?? correct value of deffreevars for records?
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return $ if iscon then ccon else c
  _ -> do
   cmap <- fst `liftM` gets sConsts
   case Map.lookup name cmap of
    Just (mode', c) ->
     return c
    Nothing -> do
     (miscon, sname) <- if iscon then do
       let MB.Constructor {MB.conPars = npar, MB.conData = dname} = MB.theDef def
       return (Just npar, show dname ++ "." ++ show (I.qnameName name))
      else
       return (Nothing, show name)
     mainm <- gets sMainMeta
     dfv <- lift $ getdfv mainm name
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = sname, cdorigin = (miscon, name), cdtype = __IMPOSSIBLE__, cdcont = __IMPOSSIBLE__, cddeffreevars = dfv})
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return c

getdfv mainm name = do
 mv <- lookupMeta mainm
 withMetaInfo (getMetaInfo mv) $ getDefFreeVars name

getMeta :: I.MetaId -> TOM (Metavar (Exp O) (RefInfo O))
getMeta name = do
 mmap <- fst `liftM` gets sMetas
 case Map.lookup name mmap of
  Just (m, _, _) ->
   return m
  Nothing -> do
   m <- lift $ liftIO initMeta
   modify (\s -> s {sMetas = (Map.insert name (m, Nothing, []) mmap, name : snd (sMetas s))})
   return m

getEqs :: MB.TCM [(Bool, I.Term, I.Term)]
getEqs = do
 eqs <- getAllConstraints
 let r = mapM (\eqc -> do
          neqc <- norm eqc
          case MB.clValue $ MB.theConstraint neqc of
           MB.ValueCmp ineq _ i e -> do
            ei <- etaContract i
            ee <- etaContract e
            return [(tomyIneq ineq, ee, ei)]
           MB.TypeCmp ineq i e -> do
            I.El _ ei <- etaContract i
            I.El _ ee <- etaContract e
            return [(tomyIneq ineq, ee, ei)]
           MB.Guarded (MB.UnBlock _) pid -> return []
           _ -> return []
         )
 eqs' <- r eqs
 return $ concat eqs'


tomyClauses [] = return []
tomyClauses (cl:cls) = do
 cl' <- tomyClause cl
 cls' <- tomyClauses cls
 return $ case cl' of
  Just cl' -> cl' : cls'
  Nothing -> cls'

tomyClause cl@(I.Clause {I.clausePerm = Perm n ps, I.clausePats = pats, I.clauseBody = body}) = do
 pats' <- mapM tomyPat pats
 body' <- tomyBody body
 return $ case body' of
           Just (body', _) -> Just (pats', body')
           Nothing -> Nothing

tomyPat p = case C.unArg p of
 I.VarP n -> return $ PatVar (show n)
 I.DotP _ -> return $ PatVar "_" -- because Agda includes these when referring to variables in the body
 I.ConP n _ pats -> do
  c <- getConst True n TMAll
  pats' <- mapM tomyPat pats
  def <- lift $ getConstInfo n
  cc <- lift $ liftIO $ readIORef c
  let Just npar = fst $ cdorigin cc
  return $ PatConApp c (replicate npar PatExp ++ pats')
 I.LitP _ -> throwError $ strMsg "Auto: Literals in patterns are not supported"

tomyBody (I.Body t) = do
 t <- lift $ norm t
 t' <- tomyExp t
 return $ Just (t', 0)
tomyBody (I.Bind (I.Abs _ b)) = do
 res <- tomyBody b
 return $ case res of
  Nothing -> Nothing
  Just (b', i) -> Just (b', i + 1)
tomyBody (I.Bind (I.NoAbs _ b)) = tomyBody b
tomyBody I.NoBody = return Nothing

weaken :: Int -> MExp O -> MExp O
weaken _ e@(Meta m) = e
weaken i (NotM e) =
 case e of
  App uid okh elr as ->
   let elr' = case elr of
               Var v -> if v >= i then Var (v + 1) else elr
               Const{} -> elr
       as' = weakens i as
   in NotM $ App uid okh elr' as'
  Lam hid (Abs mid t) ->
   let t' = weaken (i + 1) t
   in NotM $ Lam hid (Abs mid t')
  Pi uid hid possdep x (Abs mid y) ->
   let x' = weaken i x
       y' = weaken (i + 1) y
   in NotM $ Pi uid hid possdep x' (Abs mid y')
  Sort{} -> NotM e

  AbsurdLambda{} -> NotM e


weakens :: Int -> MArgList O -> MArgList O
weakens _ as@(Meta m) = as
weakens i (NotM as) =
 case as of
  ALNil -> NotM as
  ALCons hid x xs ->
   let x' = weaken i x
       xs' = weakens i xs
   in NotM $ ALCons hid x' xs'

  ALProj{} -> __IMPOSSIBLE__

  ALConPar xs ->
   let xs' = weakens i xs
   in NotM $ ALConPar xs'


tomyType :: I.Type -> TOM (MExp O)
tomyType (I.El _ t) = tomyExp t -- sort info is thrown away

tomyExp :: I.Term -> TOM (MExp O)
tomyExp (I.Var v as) = do
 as' <- tomyExps as
 return $ NotM $ App Nothing (NotM OKVal) (Var v) as'
tomyExp (I.Lam info b) = do
 b' <- tomyExp (I.absBody b)
 return $ NotM $ Lam (cnvh info) (Abs (Id $ I.absName b) b')
tomyExp t@(I.Lit{}) = do
 t <- lift $ constructorForm t
 case t of
  I.Lit{} -> throwError $ strMsg "Auto: Literals in terms are not supported"
  _ -> tomyExp t
tomyExp (I.Level l) = tomyExp =<< lift (reallyUnLevelView l)
tomyExp (I.Def name as) = do
 c <- getConst False name TMAll
 as' <- tomyExps as
 return $ NotM $ App Nothing (NotM OKVal) (Const c) as'
tomyExp (I.Con name as) = do
 c <- getConst True name TMAll
 as' <- tomyExps as
 def <- lift $ getConstInfo name
 cc <- lift $ liftIO $ readIORef c
 let Just npar = fst $ cdorigin cc
 return $ NotM $ App Nothing (NotM OKVal) (Const c) (foldl (\x _ -> NotM $ ALConPar x) as' [1..npar])
tomyExp (I.Pi (C.Dom info x) b) = do
 let y    = I.absBody b
     name = I.absName b
 x' <- tomyType x
 y' <- tomyType y
 return $ NotM $ Pi Nothing (cnvh info) (Agda.TypeChecking.Free.freeIn 0 y) x' (Abs (Id name) y')
tomyExp (I.Sort (I.Type (I.Max [I.ClosedLevel l]))) = return $ NotM $ Sort $ Set $ fromIntegral l
tomyExp (I.Sort _) = return $ NotM $ Sort UnknownSort
tomyExp t@I.MetaV{} = do
 t <- lift $ instantiate t
 case t of
  I.MetaV mid _ -> do
   mcurmeta <- gets sCurMeta
   case mcurmeta of
    Nothing -> return ()
    Just curmeta ->
     modify (\s -> s {sMetas = (Map.adjust (\(m, x, deps) -> (m, x, mid : deps)) curmeta (fst $ sMetas s), snd $ sMetas s)})
   m <- getMeta mid
   return $ Meta m
  _ -> tomyExp t
tomyExp (I.DontCare _) = return $ NotM $ dontCare
tomyExp (I.Shared p) = tomyExp $ I.derefPtr p

tomyExps [] = return $ NotM ALNil
tomyExps (C.Arg info a : as) = do
 a' <- tomyExp a
 as' <- tomyExps as
 return $ NotM $ ALCons (cnvh info) a' as'

tomyIneq MB.CmpEq = False
tomyIneq MB.CmpLeq = True

-- ---------------------------------------------

fmType :: I.MetaId -> I.Type -> Bool
fmType m (I.El _ t) = fmExp m t

fmExp :: I.MetaId -> I.Term -> Bool
fmExp m (I.Var _ as) = fmExps m as
fmExp m (I.Lam _ b) = fmExp m (I.unAbs b)
fmExp m (I.Lit _) = False
fmExp m (I.Level (I.Max as)) = any (fmLevel m) as
fmExp m (I.Def _ as) = fmExps m as
fmExp m (I.Con _ as) = fmExps m as
fmExp m (I.Pi x y)  = fmType m (C.unDom x) || fmType m (I.unAbs y)
fmExp m (I.Sort _) = False
fmExp m (I.MetaV mid _) = mid == m
fmExp m (I.DontCare _) = False
fmExp m (I.Shared p) = fmExp m $ I.derefPtr p

fmExps m [] = False
fmExps m (a : as) = fmExp m (C.unArg a) || fmExps m as

fmLevel :: I.MetaId -> I.PlusLevel -> Bool
fmLevel m I.ClosedLevel{} = False
fmLevel m (I.Plus _ l) = case l of
  I.MetaLevel m' _   -> m == m'
  I.NeutralLevel v   -> fmExp m v
  I.BlockedLevel _ v -> fmExp m v
  I.UnreducedLevel v -> fmExp m v

-- ---------------------------------------------

cnvh info = case C.argInfoHiding info of
    C.NotHidden -> NotHidden
    C.Instance  -> Instance
    C.Hidden    -> Hidden
icnvh h = (C.setArgInfoHiding h' C.defaultArgInfo)
    where
    h' = case h of
        NotHidden -> C.NotHidden
        Instance  -> C.Instance
        Hidden    -> C.Hidden

-- ---------------------------------------------

frommy = frommyExp

frommyType :: MExp O -> ErrorT String IO I.Type
frommyType e = do
 e' <- frommyExp e
 return $ I.El (I.mkType 0) e'  -- 0 is arbitrary, sort not read by Agda when reifying

frommyExp :: MExp O -> ErrorT String IO I.Term
frommyExp (Meta m) = do
 bind <- lift $ readIORef $ mbind m
 case bind of
  Nothing -> throwError "meta not bound"
  Just e -> frommyExp (NotM e)
frommyExp (NotM e) =
 case e of
  App _ _ (Var v) as ->
   frommyExps 0 as (I.Var v [])
  App _ _ (Const c) as -> do
   cdef <- lift $ readIORef c
   let (iscon, name) = cdorigin cdef
       (ndrop, h) = case iscon of {Just n -> (n, I.Con); Nothing -> (0, I.Def)}
   frommyExps ndrop as (h name [])
  Lam hid (Abs mid t) -> do
   t' <- frommyExp t
   return $ I.Lam (icnvh hid) (I.Abs (case mid of {NoId -> "x"; Id id -> id}) t')
  Pi _ hid _ x (Abs mid y) -> do
   x' <- frommyType x
   y' <- frommyType y
   return $ I.Pi (C.Dom (icnvh hid) x') (I.Abs (case mid of {NoId -> "x"; Id id -> id}) y')
   -- maybe have case for Pi where possdep is False which produces Fun (and has to unweaken y), return $ I.Fun (C.Arg (icnvh hid) x') y'
  Sort (Set l) ->
   return $ I.Sort (I.mkType (fromIntegral l))
  Sort Type -> __IMPOSSIBLE__
  Sort UnknownSort -> return $ I.Sort (I.mkType 0) -- hoping that it's thrown away

  AbsurdLambda hid ->
   return $ I.Lam (icnvh hid) (I.Abs abslamvarname (I.Var 0 []))


frommyExps :: Nat -> MArgList O -> I.Term -> ErrorT String IO I.Term
frommyExps ndrop (Meta m) trm = do
 bind <- lift $ readIORef $ mbind m
 case bind of
  Nothing -> throwError "meta not bound"
  Just e -> frommyExps ndrop (NotM e) trm
frommyExps ndrop (NotM as) trm =
 case as of
  ALNil -> return trm
  ALCons _ _ xs | ndrop > 0 -> frommyExps (ndrop - 1) xs trm
  ALCons hid x xs -> do
   x' <- frommyExp x
   frommyExps ndrop xs (addend (C.Arg (icnvh hid) x') trm)

  ALProj eas idx hid xs -> do
   idx <- lift $ expandbind idx
   c <- case idx of
            NotM c -> return c
            Meta{} -> throwError "meta not bound"
   cdef <- lift $ readIORef c
   let name = snd $ cdorigin cdef
   trm2 <- frommyExps 0 eas (I.Def name [])
   frommyExps 0 xs (addend (C.Arg (icnvh hid) trm) trm2)

  ALConPar xs | ndrop > 0 -> frommyExps (ndrop - 1) xs trm
  ALConPar _ -> __IMPOSSIBLE__
 where
  addend x (I.Var h xs) = I.Var h (xs ++ [x])
  addend x (I.Con h xs) = I.Con h (xs ++ [x])
  addend x (I.Def h xs) = I.Def h (xs ++ [x])
  addend x (I.Shared p) = addend x (I.derefPtr p)
  addend _ _ = __IMPOSSIBLE__

-- --------------------------------

abslamvarname = "\0absurdlambda"

modifyAbstractExpr :: A.Expr -> A.Expr
modifyAbstractExpr = f
 where
  f (A.App i e1 (C.Arg info (C.Named n e2))) =
        A.App i (f e1) (C.Arg info (C.Named n (f e2)))
  f (A.Lam i (A.DomainFree info n) _) | show n == abslamvarname =
        A.AbsurdLam i $ C.argInfoHiding info
  f (A.Lam i b e) = A.Lam i b (f e)
  f (A.Rec i xs) = A.Rec i (map (\(n, e) -> (n, f e)) xs)
  f (A.RecUpdate i e xs) = A.RecUpdate i (f e) (map (\(n, e) -> (n, f e)) xs)
  f (A.ScopedExpr i e) = A.ScopedExpr i (f e)
  f e = e

modifyAbstractClause :: A.Clause -> A.Clause
modifyAbstractClause (A.Clause lhs (A.RHS e) decls) = A.Clause lhs (A.RHS (modifyAbstractExpr e)) decls
modifyAbstractClause cl = cl

-- ---------------------------------


constructPats :: Map AN.QName (TMode, ConstRef O) -> I.MetaId -> I.Clause -> MB.TCM ([(FMode, MId)], [CSPat O])
constructPats cmap mainm clause = do
 let cnvps ns [] = return (ns, [])
     cnvps ns (p : ps) = do
      (ns', ps') <- cnvps ns ps
      (ns'', p') <- cnvp ns' p
      return (ns'', p' : ps')
     cnvp ns p =
      let hid = cnvh $ C.argInfo p
      in case C.unArg p of
       I.VarP n -> return ((hid, Id n) : ns, HI hid (CSPatVar $ length ns))
       I.ConP c _ ps -> do
        (c2, _) <- runStateT (getConst True c TMAll) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing, sMainMeta = mainm})
        (ns', ps') <- cnvps ns ps
        cc <- liftIO $ readIORef c2
        let Just npar = fst $ cdorigin cc
        return (ns', HI hid (CSPatConApp c2 (replicate npar (HI Hidden CSOmittedArg) ++ ps')))
       I.DotP t -> do
        (t2, _) <- runStateT (tomyExp t) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing, sMainMeta = mainm})
        return (ns, HI hid (CSPatExp t2))
       _ -> __IMPOSSIBLE__
 (names, pats) <- cnvps [] (I.clausePats clause)
 return (reverse names, pats)


frommyClause :: (CSCtx O, [CSPat O], Maybe (MExp O)) -> ErrorT String IO I.Clause
frommyClause (ids, pats, mrhs) = do
 let ctel [] = return I.EmptyTel
     ctel (HI hid (mid, t) : ctx) = do
      let Id id = mid
      tel <- ctel ctx
      t' <- frommyType t
      return $ I.ExtendTel (C.Dom (icnvh hid) t') (I.Abs id tel)
 tel <- ctel $ reverse ids
 let getperms 0 [] perm nv = return (perm, nv)
     getperms n [] _ _ = __IMPOSSIBLE__
     getperms 0 (p : ps) perm nv = do
      (perm, nv) <- getperm p perm nv
      getperms 0 ps perm nv
     getperms n (HI _ CSPatExp{} : ps) perm nv = getperms (n - 1) ps perm nv
     getperms n (HI _ CSOmittedArg{} : ps) perm nv = getperms (n - 1) ps perm nv
     getperms n (_ : _) _ _ = __IMPOSSIBLE__
     getperm (HI _ p) perm nv =
      case p of
       --CSPatVar v -> return (length ids + nv - 1 - v : perm, nv)
       CSPatVar v -> return ((length ids - 1 - v, nv) : perm, nv + 1)
       CSPatConApp c ps -> do
        cdef <- lift $ readIORef c
        let (Just ndrop, _) = cdorigin cdef
        getperms ndrop ps perm nv
       CSPatExp e -> return (perm, nv + 1)
       _ -> __IMPOSSIBLE__
 (rperm, nv) <- getperms 0 pats [] 0
 let --perm = reverse rperm
     perm = map (\i -> let Just x = lookup i rperm in x) [0..length ids - 1]
     --renperm = map (\i -> length ids + nv - 1 - i) rperm
     --renm = rename (\i -> renperm !! i)
     cnvps 0 [] = return []
     cnvps n [] = __IMPOSSIBLE__
     cnvps 0 (p : ps) = do
      p' <- cnvp p
      ps' <- cnvps 0 ps
      return (p' : ps')
     cnvps n (HI _ CSPatExp{} : ps) = cnvps (n - 1) ps
     cnvps n (HI _ CSOmittedArg{} : ps) = cnvps (n - 1) ps
     cnvps n (_ : _) = __IMPOSSIBLE__
     cnvp (HI hid p) = do
      p' <- case p of
       CSPatVar v -> return (I.VarP $ let HI _ (Id n, _) = ids !! v in n)
       CSPatConApp c ps -> do
        cdef <- lift $ readIORef c
        let (Just ndrop, name) = cdorigin cdef
        ps' <- cnvps ndrop ps
        return (I.ConP name Nothing ps')
       CSPatExp e -> do
        e' <- frommyExp {- renm e -} e  -- rename disabled to match (incorrect?) Agda reification of clauses
        return (I.DotP e')
       CSAbsurd -> __IMPOSSIBLE__ -- CSAbsurd not used
       _ -> __IMPOSSIBLE__
      return $ C.Arg (icnvh hid) p'
 ps <- cnvps 0 pats
 body <- case mrhs of
          Nothing -> return $ I.NoBody
          Just e -> do
           e' <- frommyExp {- renm e -} e  -- rename disabled to match (incorrect?) Agda reification of clauses
           let r 0 = I.Body e'
               r n = I.Bind $ I.Abs "h" $ r (n - 1)
               e'' = r ({-length ids + -}nv)
           return e''
 return $ I.Clause SP.noRange tel (Perm (nv{- + length ids-}) perm) ps body

contains_constructor :: [CSPat O] -> Bool
contains_constructor = any f
 where
  f (HI _ p) = case p of
         CSPatConApp{} -> True
         _ -> False


etaContractBody :: I.ClauseBody -> MB.TCM I.ClauseBody
etaContractBody (I.NoBody) = return I.NoBody
etaContractBody (I.Body b) = etaContract b >>= \b -> return (I.Body b)
etaContractBody (I.Bind (I.Abs id b)) = etaContractBody b >>= \b -> return (I.Bind (I.Abs id b))
etaContractBody (I.Bind (I.NoAbs x b))  = I.Bind . I.NoAbs x <$> etaContractBody b


-- ---------------------------------

freeIn :: Nat -> MExp o -> Bool
freeIn = f
 where
  mr x = let NotM x' = x in x'
  f v e = case mr e of
   App _ _ elr args -> case elr of
    Var v' | v' == v -> False
    _ -> fs v args
   Lam _ (Abs _ b) -> f (v + 1) b
   Pi _ _ _ it (Abs _ ot) -> f v it && f (v + 1) ot
   Sort{} -> True

   AbsurdLambda{} -> True


  fs v es = case mr es of
   ALNil -> True
   ALCons _ a as -> f v a && fs v as

   ALProj{} -> __IMPOSSIBLE__


   ALConPar as -> fs v as


negtype :: ConstRef o -> MExp o -> MExp o
negtype ee = f 0
 where
  mr x = let NotM x' = x in x'
  f n e = case mr e of
   Pi uid hid possdep it (Abs id ot) -> NotM $ Pi uid hid possdep it (Abs id (f (n + 1) ot))
   _ -> NotM $ Pi Nothing NotHidden False (NotM $ Pi Nothing NotHidden False e (Abs NoId (NotM $ Pi Nothing NotHidden True (NotM $ Sort (Set 0)) (Abs NoId (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)))))) (Abs NoId (NotM $ App Nothing (NotM OKVal) (Const ee) (NotM ALNil)))

-- ---------------------------------------

findClauseDeep :: I.MetaId -> MB.TCM (Maybe (AN.QName, I.Clause, Bool))
findClauseDeep m = do
  sig <- getImportedSignature
  let res = do
        def <- HMap.elems $ MB.sigDefinitions sig
        MB.Function{MB.funClauses = cs} <- [MB.theDef def]
        c <- cs
        unless (peelbinds False findMeta $ I.clauseBody c) []
        return (MB.defName def, c, peelbinds __IMPOSSIBLE__ toplevel $ I.clauseBody c)
  return $ case res of
    [] -> Nothing
    r:_ -> Just r   -- TODO: with pattern matching lambdas we might get more than one hit, which to choose?
  where
    peelbinds d f = r
     where r b = case b of
                  I.Bind b -> r $ I.absBody b
                  I.NoBody -> d
                  I.Body e -> f e
    findMeta e =
     case I.ignoreSharing e of
      I.Var _ as -> findMetas as
      I.Lam _ b -> findMeta (I.absBody b)
      I.Lit{} -> False
      I.Level (I.Max as) -> any (fmLevel m) as
      I.Def _ as -> findMetas as
      I.Con _ as -> findMetas as
      I.Pi it ot -> findMetat (C.unDom it) || findMetat (I.unAbs ot)
      I.Sort{} -> False
      I.MetaV m' _  -> m == m'
      I.DontCare _ -> False
      I.Shared{} -> __IMPOSSIBLE__
    findMetas = any (findMeta . C.unArg)
    findMetat (I.El _ e) = findMeta e
    toplevel e =
     case I.ignoreSharing e of
      I.MetaV{} -> True
      _ -> False

-- ---------------------------------------

matchType :: Int -> Int -> I.Type -> I.Type -> Maybe (Nat, Nat) -- Nat is deffreevars of const, Nat is ctx length of target type, left arg is const type, right is target type
matchType cdfv tctx ctyp ttyp = trmodps cdfv ctyp
 where
  trmodps 0 ctyp = tr 0 0 ctyp
  trmodps n ctyp = case I.ignoreSharing $ I.unEl ctyp of
   I.Pi _ ot -> trmodps (n - 1) (I.absBody ot)
   _ -> __IMPOSSIBLE__
  tr narg na ctyp =
   case ft 0 0 Just ctyp ttyp of
    Just n -> Just (n, narg)
    Nothing -> case I.ignoreSharing $ I.unEl ctyp of
     I.Pi _ (I.Abs _ ot) -> tr (narg + 1) (na + 1) ot
     I.Pi _ (I.NoAbs _ ot) -> tr (narg + 1) na ot
     _ -> Nothing
   where
    ft nl n c (I.El _ e1) (I.El _ e2) = f nl n c e1 e2
    f nl n c e1 e2 = case I.ignoreSharing e1 of
     I.Var v1 as1 | v1 < nl -> case e2 of
      I.Var v2 as2 | v1 == v2 -> fs nl (n + 1) c as1 as2
      _ -> Nothing
     I.Var v1 _ | v1 < nl + na -> c n -- unify vars with no args?
     I.Var v1 as1 -> case e2 of
      I.Var v2 as2 | cdfv + na + nl - v1 == tctx + nl - v2 -> fs nl (n + 1) c as1 as2
      _ -> Nothing
     _ -> case (I.ignoreSharing e1, I.ignoreSharing e2) of
      (I.MetaV{}, _) -> c n
      (_, I.MetaV{}) -> c n
      (I.Lam hid1 b1, I.Lam hid2 b2) | hid1 == hid2 -> f (nl + 1) n c (I.absBody b1) (I.absBody b2)
      (I.Lit lit1, I.Lit lit2) | lit1 == lit2 -> c (n + 1)
      (I.Def n1 as1, I.Def n2 as2) | n1 == n2 -> fs nl (n + 1) c as1 as2
      (I.Con n1 as1, I.Con n2 as2) | n1 == n2 -> fs nl (n + 1) c as1 as2
      (I.Pi (C.Dom info1 it1) ot1, I.Pi (C.Dom info2 it2) ot2) | C.argInfoHiding info1 == C.argInfoHiding info2 -> ft nl n (\n -> ft (nl + 1) n c (I.absBody ot1) (I.absBody ot2)) it1 it2
      (I.Sort{}, I.Sort{}) -> c n -- sloppy
      _ -> Nothing
    fs nl n c es1 es2 = case (es1, es2) of
     ([], []) -> c n
     (C.Arg info1 e1 : es1, C.Arg info2 e2 : es2) | C.argInfoHiding info1 == C.argInfoHiding info2 -> f nl n (\n -> fs nl n c es1 es2) e1 e2
     _ -> Nothing
