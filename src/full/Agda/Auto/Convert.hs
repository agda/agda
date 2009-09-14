module Agda.Auto.Convert where

import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

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
import Agda.TypeChecking.Reduce (normalise)
import Agda.TypeChecking.EtaContract (etaContract)
--import Agda.Interaction.Monad
--import Agda.Utils.Monad.Undo

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

type O = (Bool, AN.QName)  -- false - Def, true - Con

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
            sMetas :: MapS I.MetaId (Metavar (Exp O) (RefInfo O), Maybe (MExp O, [MExp O])),
            sEqs :: MapS Int (Maybe (Bool, MExp O, MExp O))
           }

type TOM = StateT S MB.TCM

tomy :: I.MetaId -> [(Bool, AN.QName)] -> MB.TCM (Metavar (Exp O) (RefInfo O), [ConstRef O], [(Metavar (Exp O) (RefInfo O), MExp O, [MExp O])], [(Bool, MExp O, MExp O)], Map AN.QName (TMode, ConstRef O))
tomy imi icns = do
 eqs <- getEqs
 let
  r :: TOM ()
  r = do
   nxt <- popMapS sConsts (\x y -> y {sConsts = x})
   case nxt of
    Just cn -> do
     -- lift $ liftIO $ putStrLn $ "doing const: " ++ show cn
     cmap <- fst `liftM` gets sConsts
     let (mode, c) = cmap Map.! cn
     def <- lift $ getConstInfo cn
     let typ = MB.defType def
         defn = MB.theDef def
     typ <- lift $ rewrite Normalised typ
     typ' <- tomyType typ
     cont <- case defn of
      MB.Axiom {} -> return Postulate
      MB.Function {MB.funClauses = clauses} -> do
       clauses' <- mapM tomyClause clauses
       let narg = case clauses of
                   [] -> 0
                   (I.Clause {I.clausePats = xs}:_) -> length xs
       return $ Def narg clauses'
      MB.Datatype {MB.dataCons = cons} -> do
       cons' <- mapM (\con -> getConst True con TMAll) cons
       return $ Datatype cons'
 --     MB.Record {MB.recFields fields, MB.recTel tel} -> do
      MB.Constructor {} -> return Constructor
      _ -> error "record and primitive defn not supported"
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
       let HasType _ tt = mvJudgement mv
           minfo = getMetaInfo mv
           localVars = map (snd . C.unArg . ctxEntry) . envContext . clEnv $ minfo
       (targettype, localVars) <- lift $ withMetaInfo minfo $ do  -- this is needed for rewrite or getContextArgs to get in right context
        vs <- getContextArgs
        let targettype = tt `piApply` vs
        targettype <- rewrite Normalised targettype
        localVars <- mapM (rewrite Normalised) localVars
        return (targettype, localVars)
       typ' <- tomyType targettype
       ctx' <- mapM tomyType localVars
       modify (\s -> s {sMetas = (Map.adjust (\(m, Nothing) -> (m, Just (typ', ctx'))) mi (fst $ sMetas s), snd $ sMetas s)})
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
 ((imi', icns'), s) <- runStateT
  (do imi' <- getMeta imi
      icns' <- mapM (\(iscon, name) -> getConst iscon name TMAll) icns
      r
      return (imi', icns')
  ) (S {sConsts = initMapS, sMetas = initMapS, sEqs = initMapS})
 return (imi', icns', map (\(x, Just (y, z)) -> (x, y, z)) $ Map.elems (fst (sMetas s)), map (\(Just x) -> x) $ Map.elems (fst (sEqs s)), fst (sConsts s))
 where

getConst :: Bool -> AN.QName -> TMode -> TOM (ConstRef O)
getConst iscon name mode = do
 cmap <- fst `liftM` gets sConsts
 case Map.lookup name cmap of
  Just (mode', c) ->
   --let mode'' = maxMode mode mode'  -- these lines not needed when TMode is singleton
   --when (mode'' /= mode') $ modify (\(_, clst) -> (Map.insert name (mode'', c) cmap, clst))
   return c
  Nothing -> do
   c <- lift $ liftIO $ newIORef (ConstDef {cdname = show name, cdorigin = (iscon, name), cdtype = error "not initialized", cdcont = error "not initialized"})
   modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
   return c

getMeta :: I.MetaId -> TOM (Metavar (Exp O) (RefInfo O))
getMeta name = do
 mmap <- fst `liftM` gets sMetas
 case Map.lookup name mmap of
  Just (m, _) ->
   return m
  Nothing -> do
   m <- lift $ liftIO $ newMeta Nothing
   modify (\s -> s {sMetas = (Map.insert name (m, Nothing) mmap, name : snd (sMetas s))})
   return m

getEqs :: MB.TCM [(Bool, I.Term, I.Term)]
getEqs = do
 eqs <- getConstraints
 let r = mapM (\eqc -> do
          neqc <- normalise eqc
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

{-
tomy :: ([I.Type], [(Bool, AN.QName)]) -> MB.TCM (([MExp O], [ConstRef O]), [(Metavar (Exp O) (RefInfo O), [MExp O])], Map AN.QName (TMode, ConstRef O))
tomy (es, cs) = do
 (e', (cmap, clst, mmap, mlst)) <- runStateT
                        (do es' <- mapM tomyType es
                            cs' <- mapM (\(iscon, name) -> getConst iscon name TMAll) cs  -- TODO find out if Def or Con
                            return (es', cs')
                        ) (Map.empty, [], Map.empty, [])
 let r cmap [] mmap [] = return (cmap, mmap)
     r cmap (name:clst) mmap mlst = do
      let (mode, c) = cmap Map.! name
      def <- getConstInfo name
      let typ = MB.defType def
          defn = MB.theDef def
      typ <- rewrite Normalised typ
      ((typ', cont), (cmap', clst', mmap', mlst')) <- runStateT
       (do typ' <- tomyType typ
           cont <- case defn of
            MB.Axiom {} -> return Postulate
            MB.Function {MB.funClauses = clauses} -> do
             clauses' <- mapM tomyClause clauses
             let narg = case clauses of
                         [] -> 0
                         (I.Clause {I.clausePats = xs}:_) -> length xs
             return $ Def narg clauses'
            MB.Datatype {MB.dataCons = cons} -> do
             cons' <- mapM (\con -> getConst True con TMAll) cons
             return $ Datatype cons'
{-            MB.Record {MB.recFields fields, MB.recTel tel} -> do
-}
            MB.Constructor {} -> return Constructor
            _ -> error "record and primitive defn not supported"
           return (typ', cont)
       ) (cmap, clst, mmap, mlst)
      liftIO $ modifyIORef c (\cdef -> cdef {cdtype = typ', cdcont = cont})
      r cmap' clst' mmap' mlst'
     r cmap clst mmap (mid:mlst) = do
      mv <- lookupMeta mid
      let HasType _ tt = mvJudgement mv
          minfo = getMetaInfo mv
          localVars = map (snd . C.unArg . ctxEntry) . envContext . clEnv $ minfo
      withMetaInfo minfo $ do  -- this is needed for rewrite or getContextArgs to get in right context
       vs <- getContextArgs
       let targettype = tt `piApply` vs
       targettype <- rewrite Normalised targettype
       localVars <- mapM (rewrite Normalised) localVars
       ((typ', ctx'), (cmap', clst', mmap', mlst')) <- runStateT
        (do typ' <- tomyType targettype
            ctx' <- mapM tomyType localVars
            return (typ', ctx')
        ) (cmap, clst, mmap, mlst)
       let mmap'' = Map.adjust (\(m, Nothing) -> (m, Just (typ' : ctx'))) mid mmap'
       r cmap' clst' mmap'' mlst' 
 (cmap', mmap') <- r cmap clst mmap mlst
 return (e', map (\(x, Just y) -> (x, y)) $ Map.elems mmap', cmap')
-}

tomyClause I.Clause {I.clausePerm = Perm n ps, I.clausePats = pats, I.clauseBody = body} = do
 -- when (ps /= [0..n - 1]) $ lift $ liftIO $ putStrLn $ "clause permutation is not id" ++ show (n, ps)
 pats' <- mapM tomyPat pats
 body' <- tomyBody body
 return (pats', body')

tomyPat p = case C.unArg p of
 I.VarP _ -> return PatVar
 I.DotP _ -> return PatExp
 I.ConP n pats -> do
  c <- getConst True n TMAll
  pats' <- mapM tomyPat pats
  def <- lift $ getConstInfo n
  let MB.Constructor {MB.conPars = npar} = MB.theDef def
  return $ PatConApp c (replicate (fromIntegral npar) PatExp ++ pats')
 I.LitP _ -> error "tomyPat: LitP not supported"

tomyBody (I.Body t) = do
 t <- lift $ rewrite Normalised t
 tomyExp t
tomyBody (I.Bind (I.Abs _ b)) = tomyBody b
tomyBody I.NoBody = return $ error "tomyBody: absurd case"
tomyBody b = error $ "tomyBody: not supported: " ++ show b

tomyType :: I.Type -> TOM (MExp O)
tomyType (I.El _ t) = tomyExp t  -- sort info is thrown away

wr = NotM


tomyExp :: I.Term -> TOM (MExp O)
tomyExp (I.Var v as) = do
 as' <- tomyExps as
 return $ wr $ App (Var $ fromIntegral v) as'
tomyExp (I.Lam hid (I.Abs name b)) = do
 b' <- tomyExp b
 return $ wr $ Lam (cnvh hid) (Abs (Id name) b')
tomyExp (I.Def name as) = do
 c <- getConst False name TMAll
 as' <- tomyExps as
 return $ wr $ App (Const c) as'
tomyExp (I.Con name as) = do
 c <- getConst True name TMAll
 as' <- tomyExps as
 def <- lift $ getConstInfo name
 let MB.Constructor {MB.conPars = npar} = MB.theDef def
 return $ wr $ App (Const c) (foldl (\x _ -> NotM $ ALConPar x) as' [1..npar])
tomyExp (I.Pi (C.Arg hid x) (I.Abs name y)) = do
 x' <- tomyType x
 y' <- tomyType y
 return $ wr $ Pi (cnvh hid) x' (Abs (Id name) y')
tomyExp (I.Fun (C.Arg hid x) y) = do
 x' <- tomyType x
 y' <- tomyType y
 return $ wr $ Fun (cnvh hid) x' y'
tomyExp (I.Sort (I.Type l)) = return $ wr $ Sort $ SortLevel $ fromIntegral l
tomyExp (I.MetaV mid _) = do
 m <- getMeta mid
 return $ Meta m
tomyExp t = error $ "tomyExp: pattern not matched: " ++ show t  -- Lit, MetaV, other Sorts not supported

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
fmExp m (I.Def _ as) =  fmExps m as
fmExp m (I.Con _ as) =  fmExps m as
fmExp m (I.Pi (C.Arg _ x) (I.Abs _ y)) = fmType m x || fmType m y
fmExp m (I.Fun (C.Arg _ x) y) = fmType m x || fmType m y
fmExp m (I.Sort (I.Type l)) = False
fmExp m (I.MetaV mid _) = mid == m
fmExp m t = error $ "fmExp: pattern not matched: " ++ show t  -- Lit, MetaV, other Sorts not supported

fmExps m [] = False
fmExps m (C.Arg _ a : as) = fmExp m a || fmExps m as

-- ---------------------------------------------

cnvh C.NotHidden = NotHidden
cnvh C.Hidden = Hidden
icnvh NotHidden = C.NotHidden
icnvh Hidden = C.Hidden

-- ---------------------------------------------

maxMode TMAll TMAll = TMAll

-- ---------------------------------------------

frommy = frommyExp

frommyType e = do
 e' <- frommyExp e
 return $ I.El (I.Type 2{-error "Sort not read by Agda when reifying"-}) e'

frommyExp :: MExp O -> IO I.Term
frommyExp (Meta m) = do
 bind <- readIORef $ mbind m
 case bind of
  Nothing -> error "frommyExp: meta not bound"
  Just e -> frommyExp (NotM e)
frommyExp (NotM e) =
 case e of
  App (Var v) as -> do
   as' <- frommyExps as
   return $ I.Var (fromIntegral v) as'
  App (Const c) as -> do
   as' <- frommyExps as
   cdef <- readIORef c
   let (iscon, name) = cdorigin cdef
   return $ (if iscon then I.Con else I.Def) name as'
  Lam hid (Abs mid t) -> do
   t' <- frommyExp t
   return $ I.Lam (icnvh hid) (I.Abs (case mid of {NoId -> "x"; Id id -> id}) t')
  Pi hid x (Abs mid y) -> do
   x' <- frommyType x
   y' <- frommyType y
   return $ I.Pi (C.Arg (icnvh hid) x') (I.Abs (case mid of {NoId -> "x"; Id id -> id}) y')
  Fun hid x y -> do
   x' <- frommyType x
   y' <- frommyType y
   return $ I.Fun (C.Arg (icnvh hid) x') y'
  Sort (SortLevel l) ->
   return $ I.Sort (I.Type (fromIntegral l))
  _ -> error "frommyExp: pattern not matched"  -- other Sorts not supported

frommyExps :: MArgList O -> IO I.Args
frommyExps (Meta m) = do
 bind <- readIORef $ mbind m
 case bind of
  Nothing -> error "frommyExps: meta not bound"
  Just e -> frommyExps (NotM e)
frommyExps (NotM as) =
 case as of
  ALNil -> return []
  ALCons hid x xs -> do
   x' <- frommyExp x
   xs' <- frommyExps xs
   return $ C.Arg (icnvh hid) x' : xs'
  ALConPar _ -> error "ConPar should not occur here"

