

module Agda.Auto.Convert where



import Agda.Utils.Impossible
-- mode: Agda implicit arguments
-- mode: Omitted arguments, used for implicit constructor type arguments
-- mode: A sort can be unknown, used as a hack for Agda's universe polymorphism
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
import Agda.TypeChecking.Monad.Signature (getConstInfo)
import Agda.Utils.Permutation (Permutation(Perm), idP)
import Agda.Interaction.BasicOps (rewrite, Rewrite(..))
import Agda.TypeChecking.Monad.Base (mvJudgement, getMetaInfo, ctxEntry, envContext, clEnv, Judgement(HasType))
import Agda.TypeChecking.Monad.MetaVars (lookupMeta, withMetaInfo)
import Agda.TypeChecking.Monad.Context (getContextArgs)
import Agda.TypeChecking.Monad.Constraints (lookupConstraint, getConstraints)
import Agda.TypeChecking.Substitute (piApply)
import Agda.TypeChecking.Reduce (Normalise, normalise, instantiate)
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Free (freeIn)
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
     let clausesToDef clauses = do
           clauses' <- tomyClauses clauses
           let narg = case clauses of
                        [] -> 0
                        I.Clause {I.clausePats = xs} : _ -> length xs
           return $ Def narg clauses' Nothing Nothing
     cont <- case defn of
      MB.Axiom {} -> return Postulate
      MB.Function {MB.funClauses = clauses} -> clausesToDef clauses
      MB.Primitive {MB.primClauses = Just clauses} -> clausesToDef clauses
      MB.Primitive {} -> throwError $ strMsg "Auto: Primitive functions are not supported"
      MB.Datatype {MB.dataCons = cons} -> do
       cons' <- mapM (\con -> getConst True con TMAll) cons
       return $ Datatype cons'
      MB.Record {MB.recFields = fields, MB.recTel = tel} -> do -- the value of recPars seems unreliable or don't know what it signifies
       let pars n (I.El _ (I.Pi it (I.Abs _ typ))) = C.Arg (C.argHiding it) (I.Var n []) : pars (n - 1) typ
           pars _ (I.El _ _) = []
           contyp npar I.EmptyTel = I.El (I.mkType 0 {- arbitrary -}) (I.Def cn (pars (npar - 1) typ))
           contyp npar (I.ExtendTel it (I.Abs v tel)) = I.El (I.mkType 0 {- arbitrary -}) (I.Pi it (I.Abs v (contyp (npar + 1) tel)))
       contyp' <- tomyType $ contyp 0 tel
       cc <- lift $ liftIO $ readIORef c
       let Datatype [con] = cdcont cc
       lift $ liftIO $ modifyIORef con (\cdef -> cdef {cdtype = contyp'})
       return $ cdcont cc
      MB.Constructor {MB.conData = dt} -> do
       _ <- getConst False dt TMAll -- make sure that datatype is included
       return Constructor
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
 lift $ liftIO $ mapM_ categorizedecl icns'
 return (icns', Map.map (\(x, Just (y, z), w) -> (x, y, z, w)) (fst (sMetas s)), map (\(Just x) -> x) $ Map.elems (fst (sEqs s)), fst (sConsts s))

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
     ccon <- lift $ liftIO $ newIORef (ConstDef {cdname = show name ++ ".CONS", cdorigin = (Just (fromIntegral $ I.arity (MB.defType def)), name), cdtype = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 183)), cdcont = Constructor})
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = show name, cdorigin = (Nothing, name), cdtype = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 184)), cdcont = Datatype [ccon]})
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
       return (Just (fromIntegral npar), show dname ++ "." ++ show (I.qnameName name))
      else
       return (Nothing, show name)
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = sname, cdorigin = (miscon, name), cdtype = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 198)), cdcont = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 198))})
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return c

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

tomyClause cl@(I.Clause {I.clausePerm = Perm n ps, I.clausePats = pats, I.clauseBody = body}) = do
 pats' <- mapM tomyPat pats
 body' <- tomyBody body
 return $ case body' of
           Just (body', _) -> Just (pats', body')
           Nothing -> Nothing

tomyPat p = case C.unArg p of
 I.VarP n -> return $ PatVar (show n)
 I.DotP _ -> return $ PatVar "_" -- because Agda includes these when referring to variables in the body
 I.ConP n pats -> do
  c <- getConst True n TMAll
  pats' <- mapM tomyPat pats
  def <- lift $ getConstInfo n
  cc <- lift $ liftIO $ readIORef c
  let Just npar = fst $ cdorigin cc
  return $ PatConApp c (replicate (fromIntegral npar) PatExp ++ pats')
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
  ALConPar xs ->
   let xs' = weakens i xs
   in NotM $ ALConPar xs'


tomyType :: I.Type -> TOM (MExp O)
tomyType (I.El _ t) = tomyExp t -- sort info is thrown away

tomyExp :: I.Term -> TOM (MExp O)
tomyExp (I.Var v as) = do
 as' <- tomyExps as
 return $ NotM $ App Nothing (NotM OKVal) (Var $ fromIntegral v) as'
tomyExp (I.Lam hid (I.Abs name b)) = do
 b' <- tomyExp b
 return $ NotM $ Lam (cnvh hid) (Abs (Id name) b')
tomyExp t@(I.Lit{}) = do
 t <- lift $ constructorForm t
 case t of
  I.Lit{} -> throwError $ strMsg "Auto: Literals in terms are not supported"
  _ -> tomyExp t
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
tomyExp (I.Pi (C.Arg hid x) (I.Abs name y)) = do
 x' <- tomyType x
 y' <- tomyType y
 return $ NotM $ Pi Nothing (cnvh hid) (Agda.TypeChecking.Free.freeIn 0 y) x' (Abs (Id name) y')
tomyExp (I.Fun (C.Arg hid x) y) = do
 x' <- tomyType x
 y' <- tomyType y
 return $ NotM $ Pi Nothing (cnvh hid) False x' (Abs NoId (weaken 0 y'))
tomyExp (I.Sort (I.Type (I.Lit (I.LitLevel _ l)))) = return $ NotM $ Sort $ Set $ fromIntegral l
tomyExp (I.Sort (I.MetaS _ _)) = throwError $ strMsg "Auto: Searching for type place holders is not supported"
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
fmExp m (I.Def _ as) = fmExps m as
fmExp m (I.Con _ as) = fmExps m as
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
 return $ I.El (I.mkType 0) e'  -- 0 is arbitrary, sort not read by Agda when reifying
frommyExp :: MExp O -> IO I.Term
frommyExp (Meta m) = do
 bind <- readIORef $ mbind m
 case bind of
  Nothing -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 412))
  Just e -> frommyExp (NotM e)
frommyExp (NotM e) =
 case e of
  App _ _ (Var v) as -> do
   as' <- frommyExps 0 as
   return $ I.Var (fromIntegral v) as'
  App _ _ (Const c) as -> do
   cdef <- readIORef c
   let (iscon, name) = cdorigin cdef
       (ndrop, h) = case iscon of {Just n -> (n, I.Con); Nothing -> (0, I.Def)}
   as' <- frommyExps ndrop as
   return $ h name as'
  Lam hid (Abs mid t) -> do
   t' <- frommyExp t
   return $ I.Lam (icnvh hid) (I.Abs (case mid of {NoId -> "x"; Id id -> id}) t')
  Pi _ hid _ x (Abs mid y) -> do
   x' <- frommyType x
   y' <- frommyType y
   return $ I.Pi (C.Arg (icnvh hid) x') (I.Abs (case mid of {NoId -> "x"; Id id -> id}) y')
   -- maybe have case for Pi where possdep is False which produces Fun (and has to unweaken y), return $ I.Fun (C.Arg (icnvh hid) x') y'
  Sort (Set l) ->
   return $ I.Sort (I.mkType (fromIntegral l))
  Sort UnknownSort -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 435))
  Sort Type -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 436))

  AbsurdLambda hid ->
   return $ I.Lam (icnvh hid) (I.Abs abslamvarname (I.Var 0 []))


frommyExps :: Nat -> MArgList O -> IO I.Args
frommyExps ndrop (Meta m) = do
 bind <- readIORef $ mbind m
 case bind of
  Nothing -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 446))
  Just e -> frommyExps ndrop (NotM e)
frommyExps ndrop (NotM as) =
 case as of
  ALNil -> return []
  ALCons _ _ xs | ndrop > 0 -> frommyExps (ndrop - 1) xs
  ALCons hid x xs -> do
   x' <- frommyExp x
   xs' <- frommyExps ndrop xs
   return $ C.Arg (icnvh hid) x' : xs'
  ALConPar _ -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 456))

-- --------------------------------

abslamvarname = "\0absurdlambda"

modifyAbstractExpr :: A.Expr -> A.Expr
modifyAbstractExpr = f
 where
  f (A.App i e1 (C.Arg h (C.Named n e2))) = A.App i (f e1) (C.Arg h (C.Named n (f e2)))
  f (A.Lam i (A.DomainFree h n) _) | show n == abslamvarname = A.AbsurdLam i h
  f (A.Lam i b e) = A.Lam i b (f e)
  f (A.Rec i xs) = A.Rec i (map (\(n, e) -> (n, f e)) xs)
  f (A.ScopedExpr i e) = A.ScopedExpr i (f e)
  f e = e

modifyAbstractClause :: A.Clause -> A.Clause
modifyAbstractClause (A.Clause lhs (A.RHS e) decls) = A.Clause lhs (A.RHS (modifyAbstractExpr e)) decls
modifyAbstractClause cl = cl

-- ---------------------------------


constructPats :: Map AN.QName (TMode, ConstRef O) -> I.Clause -> MB.TCM ([(FMode, MId)], [CSPat O])
constructPats cmap clause = do
 let cnvps ns [] = return (ns, [])
     cnvps ns (p : ps) = do
      (ns', ps') <- cnvps ns ps
      (ns'', p') <- cnvp ns' p
      return (ns'', p' : ps')
     cnvp ns p =
      let hid = cnvh $ C.argHiding p
      in case C.unArg p of
       I.VarP n -> return ((hid, Id n) : ns, HI hid (CSPatVar $ length ns))
       I.ConP c ps -> do
        (c', _) <- runStateT (getConst True c TMAll) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing})
        (ns', ps') <- cnvps ns ps
        cc <- liftIO $ readIORef c'
        let Just npar = fst $ cdorigin cc
        return (ns', HI hid (CSPatConApp c' (replicate (fromIntegral npar) (HI Hidden CSOmittedArg) ++ ps')))
       I.DotP t -> do
        (t', _) <- runStateT (tomyExp t) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing})
        return (ns, HI hid (CSPatExp t'))
       _ -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 499))
 (names, pats) <- cnvps [] (I.clausePats clause)
 return (reverse names, pats)


frommyClause :: (CSCtx O, [CSPat O], Maybe (MExp O)) -> IO I.Clause
frommyClause (ids, pats, mrhs) = do
 let ctel [] = return I.EmptyTel
     ctel (HI hid (mid, t) : ctx) = do
      let Id id = mid
      tel <- ctel ctx
      t' <- frommyType t
      return $ I.ExtendTel (C.Arg (icnvh hid) t') (I.Abs id tel)
 tel <- ctel $ reverse ids
 let getperms 0 [] perm nv = return (perm, nv)
     getperms n [] _ _ = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 514))
     getperms 0 (p : ps) perm nv = do
      (perm, nv) <- getperm p perm nv
      getperms 0 ps perm nv
     getperms n (HI _ CSPatExp{} : ps) perm nv = getperms (n - 1) ps perm nv
     getperms n (HI _ CSOmittedArg{} : ps) perm nv = getperms (n - 1) ps perm nv
     getperms n (_ : _) _ _ = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 520))
     getperm (HI _ p) perm nv =
      case p of
       CSPatVar v -> return (length ids + nv - 1 - v : perm, nv)
       CSPatConApp c ps -> do
        cdef <- readIORef c
        let (Just ndrop, _) = cdorigin cdef
        getperms ndrop ps perm nv
       CSPatExp e -> return (perm, nv + 1)
       _ -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 529))
 (rperm, nv) <- getperms 0 pats [] 0
 let perm = reverse rperm
     renperm = map (\i -> length ids + nv - 1 - i) rperm
     renm = rename (\i -> renperm !! i)
     cnvps 0 [] = return []
     cnvps n [] = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 535))
     cnvps 0 (p : ps) = do
      p' <- cnvp p
      ps' <- cnvps 0 ps
      return (p' : ps')
     cnvps n (HI _ CSPatExp{} : ps) = cnvps (n - 1) ps
     cnvps n (HI _ CSOmittedArg{} : ps) = cnvps (n - 1) ps
     cnvps n (_ : _) = (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 542))
     cnvp (HI hid p) = do
      p' <- case p of
       CSPatVar v -> return (I.VarP $ let HI _ (Id n, _) = ids !! v in n)
       CSPatConApp c ps -> do
        cdef <- readIORef c
        let (Just ndrop, name) = cdorigin cdef
        ps' <- cnvps ndrop ps
        return (I.ConP name ps')
       CSPatExp e -> do
        e' <- frommyExp {-$ renm-} e  -- rename disabled to match (incorrect?) Agda reification of clauses
        return (I.DotP e')
       CSAbsurd -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 554)) -- CSAbsurd not used
       _ -> (throwImpossible (Impossible ("agsy: " ++ "Convert.hs") 555))
      return $ C.Arg (icnvh hid) p'
 ps <- cnvps 0 pats
 body <- case mrhs of
          Nothing -> return $ I.NoBody
          Just e -> do
           e' <- frommyExp {-$ renm-} e  -- rename disabled to match (incorrect?) Agda reification of clauses
           let r 0 = I.Body e'
               r n = I.Bind $ I.Abs "h" $ r (n - 1)
               e'' = r (length ids + nv)
           return e''
 return $ I.Clause SP.noRange tel (Perm (fromIntegral $ nv + length ids) (map fromIntegral perm)) ps body

etaContractBody :: I.ClauseBody -> MB.TCM I.ClauseBody
etaContractBody (I.NoBody) = return I.NoBody
etaContractBody (I.Body b) = etaContract b >>= \b -> return (I.Body b)
etaContractBody (I.NoBind b) = etaContractBody b >>= \b -> return (I.NoBind b)
etaContractBody (I.Bind (I.Abs id b)) = etaContractBody b >>= \b -> return (I.Bind (I.Abs id b))


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

   ALConPar as -> fs v as


negtype :: MExp o -> MExp o
negtype = f 0
 where
  mr x = let NotM x' = x in x'
  f n e = case mr e of
   Pi uid hid possdep it (Abs id ot) -> NotM $ Pi uid hid possdep it (Abs id (f (n + 1) ot))
   _ -> NotM $ Pi Nothing NotHidden False (NotM $ Pi Nothing NotHidden False e (Abs NoId (NotM $ Pi Nothing NotHidden True (NotM $ Sort (Set 0)) (Abs NoId (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)))))) (Abs NoId (NotM $ App Nothing (NotM OKVal) (Var (n + 1)) (NotM ALNil)))
