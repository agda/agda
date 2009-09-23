module Agda.Auto.Convert where

import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Error

import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Common as C
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.TypeChecking.Monad.Base as MB
import Agda.TypeChecking.Monad.Signature (getConstInfo)
import Agda.Utils.Permutation (Permutation(Perm))
import Agda.Interaction.BasicOps (rewrite, Rewrite(..))
import Agda.TypeChecking.Monad.Base (mvJudgement, getMetaInfo, ctxEntry, envContext, clEnv, Judgement(HasType))
import Agda.TypeChecking.Monad.MetaVars (lookupMeta, withMetaInfo)
import Agda.TypeChecking.Monad.Context (getContextArgs)
import Agda.TypeChecking.Monad.Constraints (lookupConstraint, getConstraints)
import Agda.TypeChecking.Substitute (piApply)
import Agda.TypeChecking.Reduce (Normalise, normalise)
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Free (freeIn)

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax


norm :: Normalise t => t -> MB.TCM t
norm x = normalise x

type O = (Maybe Int, AN.QName)  -- Nothing - Def, Just npar - Con with npar parameters which don't appear in Agda

data TMode = TMAll  -- can be extended to distinguish between different modes (all, only def)
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
            sCurMeta :: Maybe I.MetaId
           }

type TOM = StateT S MB.TCM

tomy :: I.MetaId -> [(Bool, AN.QName)] -> MB.TCM ([ConstRef O], Map I.MetaId (Metavar (Exp O) (RefInfo O), MExp O, [MExp O], [I.MetaId]), [(Bool, MExp O, MExp O)], Map AN.QName (TMode, ConstRef O))
tomy imi icns = do
 eqs <- getEqs
 let
  r :: TOM ()
  r = do
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
     cont <- case defn of
      MB.Axiom {} -> return Postulate
      MB.Function {MB.funClauses = clauses} -> do
       clauses' <- tomyClauses clauses
       let narg = case clauses of
                   [] -> 0
                   (I.Clause {I.clausePats = xs}:_) -> length xs
       return $ Def narg clauses'
      MB.Datatype {MB.dataCons = cons} -> do
       cons' <- mapM (\con -> getConst True con TMAll) cons
       return $ Datatype cons'
      MB.Record {MB.recFields = fields, MB.recTel = tel} -> do  -- the value of recPars seems unreliable or don't know what it signifies
       let pars n (I.El _ (I.Pi it (I.Abs _ typ))) = C.Arg (C.argHiding it) (I.Var n []) : pars (n - 1) typ
           pars _ (I.El _ _) = []
           contyp npar I.EmptyTel = I.El undefined (I.Def cn (pars (npar - 1) typ))
           contyp npar (I.ExtendTel it (I.Abs v tel)) = I.El undefined (I.Pi it (I.Abs v (contyp (npar + 1) tel)))
       contyp' <- tomyType $ contyp 0 tel
       cc <- lift $ liftIO $ readIORef c
       let Datatype [con] = cdcont cc
       lift $ liftIO $ modifyIORef con (\cdef -> cdef {cdtype = contyp'})
       return $ cdcont cc
      MB.Constructor {} -> return Constructor
      MB.Primitive {} -> throwError $ strMsg "Primitive functions are not supported"
     lift $ liftIO $ modifyIORef c (\cdef -> cdef {cdtype = typ', cdcont = cont})
     r
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
                       args  <- getContextArgs
                       sol <- norm (I.MetaV mi args)
                       return $ Just sol
                     _ -> return Nothing
       case msol of
        Nothing -> return ()
        Just sol -> do
         m <- getMeta mi
         sol' <- tomyExp sol
         modify $ \s -> s {sEqs = (Map.insert (Map.size (fst $ sEqs s)) (Just (False, Meta m, sol')) (fst $ sEqs s), snd $ sEqs s)}
       let HasType _ tt = mvJudgement mv
           minfo = getMetaInfo mv
           localVars = map (snd . C.unArg . ctxEntry) . envContext . clEnv $ minfo
       (targettype, localVars) <- lift $ withMetaInfo minfo $ do
        vs <- getContextArgs
        let targettype = tt `piApply` vs
        targettype <- norm targettype
        localVars <- mapM norm localVars
        return (targettype, localVars)
       modify (\s -> s {sCurMeta = Just mi})
       typ' <- tomyType targettype
       ctx' <- mapM tomyType localVars
       modify (\s -> s {sCurMeta = Nothing})
       modify (\s -> s {sMetas = (Map.adjust (\(m, Nothing, deps) -> (m, Just (typ', ctx'), deps)) mi (fst $ sMetas s), snd $ sMetas s)})
       r
      Nothing -> do
       nxt <- popMapS sEqs (\x y -> y {sEqs = x})
       case nxt of
        Just eqi -> do
         let (ineq, e, i) = eqs !! eqi
         e' <- tomyExp e
         i' <- tomyExp i
         modify (\s -> s {sEqs = (Map.adjust (\Nothing -> Just (ineq, e', i')) eqi (fst $ sEqs s), snd $ sEqs s)})
         r
        Nothing ->
         return ()
 (icns', s) <- runStateT
  (do _ <- getMeta imi
      icns' <- mapM (\(iscon, name) -> getConst iscon name TMAll) icns
      r
      return icns'
  ) (S {sConsts = initMapS, sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing})
 return (icns', Map.map (\(x, Just (y, z), w) -> (x, y, z, w)) (fst (sMetas s)), map (\(Just x) -> x) $ Map.elems (fst (sEqs s)), fst (sConsts s))
 where

getConst :: Bool -> AN.QName -> TMode -> TOM (ConstRef O)
getConst iscon name mode = do
 def <- lift $ getConstInfo name
 case MB.theDef def of
  MB.Record{} -> do
   cmap <- fst `liftM` gets sConsts
   case Map.lookup name cmap of
    Just (mode', c) ->
     if iscon then do
      cd <- lift $ liftIO $ readIORef c
      let Datatype [con] = cdcont cd
      return con
     else
      return c
    Nothing -> do
     def <- lift $ getConstInfo name
     ccon <- lift $ liftIO $ newIORef (ConstDef {cdname = show name, cdorigin = (Just (fromIntegral $ I.arity (MB.defType def)), name), cdtype = undefined, cdcont = Constructor})
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = show name, cdorigin = (Nothing, name), cdtype = undefined, cdcont = Datatype [ccon]})
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return $ if iscon then ccon else c
  _ -> do
   cmap <- fst `liftM` gets sConsts
   case Map.lookup name cmap of
    Just (mode', c) ->
     return c
    Nothing -> do
     iscon' <- if iscon then do
       def <- lift $ getConstInfo name
       let MB.Constructor {MB.conPars = npar} = MB.theDef def
       return $ Just $ fromIntegral npar
      else
       return Nothing
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = show name, cdorigin = (iscon', name), cdtype = undefined, cdcont = undefined})
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return c

getMeta :: I.MetaId -> TOM (Metavar (Exp O) (RefInfo O))
getMeta name = do
 mmap <- fst `liftM` gets sMetas
 case Map.lookup name mmap of
  Just (m, _, _) ->
   return m
  Nothing -> do
   m <- lift $ liftIO $ newMeta Nothing
   modify (\s -> s {sMetas = (Map.insert name (m, Nothing, []) mmap, name : snd (sMetas s))})
   return m

getEqs :: MB.TCM [(Bool, I.Term, I.Term)]
getEqs = do
 eqs <- getConstraints
 let r = mapM (\eqc -> do
          neqc <- norm eqc
          case MB.clValue neqc of
           MB.ValueCmp ineq _ i e -> do
            ei <- etaContract i
            ee <- etaContract e
            return [(tomyIneq ineq, ee, ei)]
           MB.TypeCmp ineq i e -> do
            I.El _ ei <- etaContract i
            I.El _ ee <- etaContract e
            return [(tomyIneq ineq, ee, ei)]
           MB.Guarded (MB.UnBlock _) cs -> do
            eqs' <- r cs
            return $ concat eqs'
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

tomyClause I.Clause {I.clausePerm = Perm n ps, I.clausePats = pats, I.clauseBody = body} = do
 pats' <- mapM tomyPat pats
 body' <- tomyBody body
 return $ case body' of
           Just (body', _) -> Just (pats', body')
           Nothing -> Nothing

tomyPat p = case C.unArg p of
 I.VarP _ -> return PatVar
 I.DotP _ -> return PatExp
 I.ConP n pats -> do
  c <- getConst True n TMAll
  pats' <- mapM tomyPat pats
  def <- lift $ getConstInfo n
  cc <- lift $ liftIO $ readIORef c
  let Just npar = fst $ cdorigin cc
  return $ PatConApp c (replicate (fromIntegral npar) PatExp ++ pats')
 I.LitP _ -> throwError $ strMsg "Literals in patterns are not supported"

tomyBody (I.Body t) = do
 t <- lift $ norm t
 t' <- tomyExp t
 return $ Just (t', 0)
tomyBody (I.Bind (I.Abs _ b)) = do
 res <- tomyBody b
 return $ case res of
  Nothing -> Nothing
  Just (b', i) -> Just (b', i + 1)
tomyBody (I.NoBind b) = do
 res <- tomyBody b
 return $ case res of
  Nothing -> Nothing
  Just (b', i) -> Just (weaken i b', i + 1)
tomyBody I.NoBody = return Nothing

weaken :: Int -> MExp O -> MExp O
weaken _ e@(Meta m) = e
weaken i (NotM e) =
 case e of
  App elr as ->
   let elr' = case elr of
               Var v -> if v >= i then Var (v + 1) else elr
               Const{} -> elr
       as' = weakens i as
   in  NotM $ App elr' as'
  Lam hid (Abs mid t) ->
   let t' = weaken (i + 1) t
   in  NotM $ Lam hid (Abs mid t')
  Pi hid possdep x (Abs mid y) -> 
   let x' = weaken i x
       y' = weaken (i + 1) y
   in  NotM $ Pi hid possdep x' (Abs mid y')
  Fun hid x y ->
   let x' = weaken i x
       y' = weaken i y
   in  NotM $ Fun hid x' y'
  Sort{} -> NotM e

weakens :: Int -> MArgList O -> MArgList O
weakens _ as@(Meta m) = as
weakens i (NotM as) =
 case as of
  ALNil -> NotM as
  ALCons hid x xs ->
   let x' = weaken i x
       xs' = weakens i xs
   in  NotM $ ALCons hid x' xs'
  ALConPar xs ->
   let xs' = weakens i xs
   in  NotM $ ALConPar xs'


tomyType :: I.Type -> TOM (MExp O)
tomyType (I.El _ t) = tomyExp t  -- sort info is thrown away

tomyExp :: I.Term -> TOM (MExp O)
tomyExp (I.Var v as) = do
 as' <- tomyExps as
 return $ NotM $ App (Var $ fromIntegral v) as'
tomyExp (I.Lam hid (I.Abs name b)) = do
 b' <- tomyExp b
 return $ NotM $ Lam (cnvh hid) (Abs (Id name) b')
tomyExp t@(I.Lit{}) = do
 t <- lift $ constructorForm t
 case t of
  I.Lit{} -> throwError $ strMsg "Literals in terms are not supported"
  _ -> tomyExp t
tomyExp (I.Def name as) = do
 c <- getConst False name TMAll
 as' <- tomyExps as
 return $ NotM $ App (Const c) as'
tomyExp (I.Con name as) = do
 c <- getConst True name TMAll
 as' <- tomyExps as
 def <- lift $ getConstInfo name
 cc <- lift $ liftIO $ readIORef c
 let Just npar = fst $ cdorigin cc
 return $ NotM $ App (Const c) (foldl (\x _ -> NotM $ ALConPar x) as' [1..npar])
tomyExp (I.Pi (C.Arg hid x) (I.Abs name y)) = do
 x' <- tomyType x
 y' <- tomyType y
 return $ NotM $ Pi (cnvh hid) (freeIn 0 y) x' (Abs (Id name) y')
tomyExp (I.Fun (C.Arg hid x) y) = do
 x' <- tomyType x
 y' <- tomyType y
 return $ NotM $ Fun (cnvh hid) x' y'
tomyExp (I.Sort (I.Type l)) = return $ NotM $ Sort $ SortLevel $ fromIntegral l
tomyExp (I.Sort (I.MetaS _)) = throwError $ strMsg "Searching for type place holders is not supported"
tomyExp t@(I.Sort _) = throwError $ strMsg $ "Meta variable kind not supported: " ++ show t
tomyExp (I.MetaV mid _) = do
 mcurmeta <- gets sCurMeta
 case mcurmeta of
  Nothing -> return ()
  Just curmeta ->
   modify (\s -> s {sMetas = (Map.adjust (\(m, x, deps) -> (m, x, mid : deps)) curmeta (fst $ sMetas s), snd $ sMetas s)})
 m <- getMeta mid
 return $ Meta m

tomyExps [] = return $ NotM ALNil
tomyExps (C.Arg hid a : as) = do
 a' <- tomyExp a
 as' <- tomyExps as
 return $ NotM $ ALCons (cnvh hid) a' as'

tomyIneq MB.CmpEq = False
tomyIneq MB.CmpLeq = True

-- ---------------------------------------------

fmType :: I.MetaId -> I.Type -> Bool
fmType m (I.El _ t) = fmExp m t

fmExp :: I.MetaId -> I.Term -> Bool
fmExp m (I.Var _ as) = fmExps m as
fmExp m (I.Lam _ (I.Abs _ b)) = fmExp m b
fmExp m (I.Lit _) = False
fmExp m (I.Def _ as) =  fmExps m as
fmExp m (I.Con _ as) =  fmExps m as
fmExp m (I.Pi (C.Arg _ x) (I.Abs _ y)) = fmType m x || fmType m y
fmExp m (I.Fun (C.Arg _ x) y) = fmType m x || fmType m y
fmExp m (I.Sort _) = False
fmExp m (I.MetaV mid _) = mid == m

fmExps m [] = False
fmExps m (C.Arg _ a : as) = fmExp m a || fmExps m as

-- ---------------------------------------------

cnvh C.NotHidden = NotHidden
cnvh C.Hidden = Hidden
icnvh NotHidden = C.NotHidden
icnvh Hidden = C.Hidden

-- ---------------------------------------------

frommy = frommyExp

frommyType e = do
 e' <- frommyExp e
 return $ I.El (I.Type 0) e'  -- 0 is arbitrary, sort no read by Agda when reifying

frommyExp :: MExp O -> IO I.Term
frommyExp (Meta m) = do
 bind <- readIORef $ mbind m
 case bind of
  Nothing -> error "frommyExp: meta not bound"
  Just e -> frommyExp (NotM e)
frommyExp (NotM e) =
 case e of
  App (Var v) as -> do
   as' <- frommyExps 0 as
   return $ I.Var (fromIntegral v) as'
  App (Const c) as -> do
   cdef <- readIORef c
   let (iscon, name) = cdorigin cdef
       (ndrop, h) = case iscon of {Just n -> (n, I.Con); Nothing -> (0, I.Def)}
   as' <- frommyExps ndrop as
   return $ h name as'
  Lam hid (Abs mid t) -> do
   t' <- frommyExp t
   return $ I.Lam (icnvh hid) (I.Abs (case mid of {NoId -> "x"; Id id -> id}) t')
  Pi hid _ x (Abs mid y) -> do
   x' <- frommyType x
   y' <- frommyType y
   return $ I.Pi (C.Arg (icnvh hid) x') (I.Abs (case mid of {NoId -> "x"; Id id -> id}) y')
  Fun hid x y -> do
   x' <- frommyType x
   y' <- frommyType y
   return $ I.Fun (C.Arg (icnvh hid) x') y'
  Sort (SortLevel l) ->
   return $ I.Sort (I.Type (fromIntegral l))
  Sort Type -> error "frommyExp: Sort Type encountered"

frommyExps :: Nat -> MArgList O -> IO I.Args
frommyExps ndrop (Meta m) = do
 bind <- readIORef $ mbind m
 case bind of
  Nothing -> error "frommyExps: meta not bound"
  Just e -> frommyExps ndrop (NotM e)
frommyExps ndrop (NotM as) =
 case as of
  ALNil -> return []
  ALCons _ _ xs | ndrop > 0 -> frommyExps (ndrop - 1) xs
  ALCons hid x xs -> do
   x' <- frommyExp x
   xs' <- frommyExps ndrop xs
   return $ C.Arg (icnvh hid) x' : xs'
  ALConPar _ -> error "ConPar should not occur here"

