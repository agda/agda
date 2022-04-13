
module Agda.Auto.Convert where

import Prelude hiding ((!!))

import Control.Monad          ( when )
import Control.Monad.Except
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.State

import Data.Bifunctor (first)
import Data.IORef
import Data.Maybe (catMaybes)
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Common (Hiding(..), getHiding, Arg)
import Agda.Syntax.Concrete (exprFieldA)
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Internal (Dom'(..),domInfo,unDom)
import qualified Agda.Syntax.Internal.Pattern as IP
import qualified Agda.Syntax.Common as Cm
import qualified Agda.Syntax.Abstract.Name as AN
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Position as SP

import qualified Agda.TypeChecking.Monad.Base as MB

import Agda.TypeChecking.Monad.Signature (getConstInfo, getDefFreeVars, ignoreAbstractMode)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Monad.Base (mvJudgement, mvPermutation, getMetaInfo, envContext, clEnv)
import Agda.TypeChecking.Monad.MetaVars
  (lookupMeta, withMetaInfo, lookupInteractionPoint)
import Agda.TypeChecking.Monad.Context (getContextArgs)
import Agda.TypeChecking.Monad.Constraints (getAllConstraints)
import Agda.TypeChecking.Substitute (applySubst, renamingR)
import Agda.TypeChecking.Telescope (piApplyM)
import qualified Agda.TypeChecking.Substitute as I (absBody)
import Agda.TypeChecking.Reduce (normalise, instantiate)
import Agda.TypeChecking.EtaContract (etaContract)
import Agda.TypeChecking.Monad.Builtin (constructorForm)
import Agda.TypeChecking.Free as Free (freeIn)

import Agda.Interaction.MakeCase (getClauseZipperForIP)

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax hiding (getConst)

import Agda.Auto.CaseSplit hiding (lift)

import Agda.Utils.Either
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Monad       ( forMaybeMM )
import Agda.Utils.Permutation ( Permutation(Perm), permute, takeP, compactP )
import Agda.Utils.Pretty      ( prettyShow )

import Agda.Utils.Impossible


data Hint = Hint
  { hintIsConstructor :: Bool
  , hintQName         :: I.QName
  }

type O = (Maybe (Int, [Arg AN.QName]),AN.QName)
  -- Nothing - Def
  -- Just npar - Con with npar parameters which don't appear in Agda

data TMode = TMAll -- can be extended to distinguish between different modes (all, only def)
 deriving Eq

type MapS a b = (Map a b, [a])

initMapS :: MapS a b
initMapS = (Map.empty, [])

popMapS :: (S -> (a, [b])) -> ((a, [b]) -> S -> S) -> TOM (Maybe b)
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
type MOT = ExceptT String IO

tomy :: I.MetaId -> [Hint] -> [I.Type] ->
        MB.TCM ([ConstRef O]
               , [MExp O]
               , Map I.MetaId (Metavar (Exp O) (RefInfo O), MExp O, [MExp O], [I.MetaId])
               , [(Bool, MExp O, MExp O)]
               , Map AN.QName (TMode, ConstRef O))
tomy imi icns typs = do
 eqs <- getEqs
 let
  r :: [AN.QName] -> TOM [AN.QName]
  r projfcns = do
   nxt <- popMapS sConsts (\x y -> y {sConsts = x})
   case nxt of
    Just cn -> do
     cmap <- gets (fst . sConsts)
     let (mode, c) = cmap Map.! cn
     def <- lift $ getConstInfo cn
     let typ = MB.defType def
         defn = MB.theDef def
     typ <- lift $ normalise typ
     typ' <- convert typ
     let clausesToDef clauses = do
           clauses' <- convert clauses
           let narg = case clauses of
                        [] -> 0
                        I.Clause {I.namedClausePats = xs} : _ -> length xs
           return (Def narg clauses' Nothing Nothing, [])
     (cont, projfcns2) <- case defn of
      MB.Axiom {} -> return (Postulate, [])
      MB.DataOrRecSig{} -> return (Postulate, [])
      MB.GeneralizableVar{} -> __IMPOSSIBLE__
      MB.AbstractDefn{} -> return (Postulate, [])
      MB.Function {MB.funClauses = clauses} -> clausesToDef clauses
      -- MB.Primitive {MB.primClauses = []} -> throwError $ strMsg "Auto: Primitive functions are not supported" -- Andreas, 2013-06-17 breaks interaction/AutoMisc
      MB.Primitive {MB.primClauses = clauses} -> clausesToDef clauses
      MB.PrimitiveSort{} -> __IMPOSSIBLE__
      MB.Datatype {MB.dataCons = cons} -> do
       cons2 <- mapM (\con -> getConst True con TMAll) cons
       return (Datatype cons2 [], [])
      MB.Record {MB.recFields = fields, MB.recTel = tel} -> do -- the value of recPars seems unreliable or don't know what it signifies
       let pars n (I.El _ (I.Pi it typ)) = Cm.Arg (I.domInfo it) (I.var n) :
                                           pars (n - 1) (I.unAbs typ)
           pars _ (I.El _ _) = []
           contyp npar I.EmptyTel = I.El (I.mkType 0 {- arbitrary -}) $
                                      I.Def cn $ map I.Apply $ pars (npar - 1) typ
           contyp npar (I.ExtendTel it (I.Abs v tel)) = I.El (I.mkType 0 {- arbitrary -}) (I.Pi it (I.Abs v (contyp (npar + 1) tel)))
           contyp npar (I.ExtendTel it I.NoAbs{})     = __IMPOSSIBLE__
       contyp' <- convert $ contyp 0 tel
       cc <- lift $ liftIO $ readIORef c
       let Datatype [con] [] = cdcont cc
       lift $ liftIO $ modifyIORef con (\cdef -> cdef {cdtype = contyp'})

       projfcns <- mapM (\ dom -> getConst False (I.unDom dom) TMAll) fields
       -- Equivalently projfcns <- mapM (($ TMAll) . getConst False . I.unDom) fields

       return (Datatype [con] projfcns, []{-map snd fields-})
      MB.Constructor {MB.conData = dt} -> do
       _ <- getConst False dt TMAll -- make sure that datatype is included
       cc <- lift $ liftIO $ readIORef c
       let (Just (nomi,_), _) = cdorigin cc
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
       mv <- lift $ lookupLocalMetaAuto mi
       msol <- case MB.mvInstantiation mv of
                     MB.InstV{} ->
                      lift $ withMetaInfo (getMetaInfo mv) $ do
                       args <- getContextArgs
                       --sol <- norm (I.MetaV mi args)
                       sol <- instantiate $ I.MetaV mi $ map I.Apply $ permute (takeP (length args) $ mvPermutation mv) args
                       return $ Just sol
                     _ -> return Nothing
       case msol of
        Nothing -> return ()
        Just sol -> do
         m <- getMeta mi
         sol' <- convert sol
         modify $ \s -> s {sEqs = first (Map.insert (Map.size (fst $ sEqs s)) (Just (False, Meta m, sol'))) (sEqs s)}
       let tt = MB.jMetaType $ mvJudgement mv
           minfo = getMetaInfo mv
           localVars = map (snd . I.unDom) . envContext . clEnv $ minfo
       (targettype, localVars) <- lift $ withMetaInfo minfo $ do
        vs <- getContextArgs
        targettype <- tt `piApplyM` permute (takeP (length vs) $ mvPermutation mv) vs
        targettype <- normalise targettype
        localVars <- mapM normalise localVars
        return (targettype, localVars)
       modify (\s -> s {sCurMeta = Just mi})
       typ' <- convert targettype
       ctx' <- mapM convert localVars
       modify (\s -> s {sCurMeta = Nothing})
       modify (\s -> s {sMetas = first (Map.adjust (\(m, _, deps) -> (m, Just (typ', ctx'), deps)) mi) (sMetas s)})
       r projfcns
      Nothing -> do
       nxt <- popMapS sEqs (\x y -> y {sEqs = x})
       case nxt of
        Just eqi -> do
         let (ineq, e, i) = eqs !! eqi
         e' <- convert e
         i' <- convert i
         modify (\s -> s {sEqs = first (Map.adjust (\_ -> Just (ineq, e', i')) eqi) (sEqs s)})
         r projfcns
        Nothing ->
         return projfcns
 ((icns', typs'), s) <- runStateT
  (do _ <- getMeta imi
      icns' <- mapM (\ (Hint iscon name) -> getConst iscon name TMAll) icns
      typs' <- mapM convert typs
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
  MB.Record {MB.recConHead = con} -> do
   let conname = I.conName con
       conflds = I.conFields con
   cmap <- gets (fst . sConsts)
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
     ccon <- lift $ liftIO $ newIORef (ConstDef {cdname = prettyShow name ++ ".CONS", cdorigin = (Just (nomi,conflds), conname), cdtype = __IMPOSSIBLE__, cdcont = Constructor (nomi - dfv), cddeffreevars = dfv}) -- ?? correct value of deffreevars for records?
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = prettyShow name, cdorigin = (Nothing, name), cdtype = __IMPOSSIBLE__, cdcont = Datatype [ccon] [], cddeffreevars = dfv}) -- ?? correct value of deffreevars for records?
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return $ if iscon then ccon else c
  _ -> do
   cmap <- gets (fst . sConsts)
   case Map.lookup name cmap of
    Just (mode', c) ->
     return c
    Nothing -> do
     (miscon, sname) <- if iscon then do
       let MB.Constructor {MB.conPars = npar, MB.conData = dname, MB.conSrcCon = ch} = MB.theDef def
       return (Just (npar,I.conFields ch), prettyShow dname ++ "." ++ prettyShow (I.qnameName name))
      else
       return (Nothing, prettyShow name)
     mainm <- gets sMainMeta
     dfv <- lift $ getdfv mainm name
     c <- lift $ liftIO $ newIORef (ConstDef {cdname = sname, cdorigin = (miscon, name), cdtype = __IMPOSSIBLE__, cdcont = __IMPOSSIBLE__, cddeffreevars = dfv})
     modify (\s -> s {sConsts = (Map.insert name (mode, c) cmap, name : snd (sConsts s))})
     return c

getdfv :: I.MetaId -> A.QName -> MB.TCM Cm.Nat
getdfv mainm name = do
 mv <- lookupLocalMetaAuto mainm
 withMetaInfo (getMetaInfo mv) $ getDefFreeVars name

-- | A variant of 'lookupLocalMeta' that, if applied to a remote
-- meta-variable, raises a special error message noting that remote
-- meta-variables are not handled by the auto command.

lookupLocalMetaAuto :: I.MetaId -> MB.TCM MB.MetaVariable
lookupLocalMetaAuto m = do
  mv <- lookupMeta m
  case mv of
    Just (Right mv) -> return mv
    Nothing         -> __IMPOSSIBLE__
    Just Left{}     -> MB.typeError $ MB.GenericError $
      "The auto command does not support remote meta-variables," ++
      "consider using --no-save-metas"

getMeta :: I.MetaId -> TOM (Metavar (Exp O) (RefInfo O))
getMeta name = do
 mmap <- gets (fst . sMetas)
 case Map.lookup name mmap of
  Just (m, _, _) ->
   return m
  Nothing -> do
   m <- lift $ liftIO initMeta
   modify $ \ s -> s { sMetas = (Map.insert name (m, Nothing, []) mmap, name : snd (sMetas s)) }
   return m

getEqs :: MB.TCM [(Bool, I.Term, I.Term)]
getEqs = forMaybeMM getAllConstraints $ \ eqc -> do
  neqc <- normalise eqc
  case MB.clValue $ MB.theConstraint neqc of
    MB.ValueCmp ineq _ i e -> do
      ei <- etaContract i
      ee <- etaContract e
      return $ Just (tomyIneq ineq, ee, ei)
    _ -> return Nothing

literalsNotImplemented :: MB.TCM a
literalsNotImplemented = MB.typeError $ MB.NotImplemented $
  "The Agda synthesizer (Agsy) does not support literals yet"

hitsNotImplemented :: MB.TCM a
hitsNotImplemented = MB.typeError $ MB.NotImplemented $
  "The Agda synthesizer (Agsy) does not support HITs yet"

class Conversion m a b where
  convert :: a -> m b

instance Conversion TOM [I.Clause] [([Pat O], MExp O)] where
  convert = fmap catMaybes . mapM convert

instance Conversion TOM I.Clause (Maybe ([Pat O], MExp O)) where
  convert cl = do
    let -- Jesper, 2016-07-28:
     -- I can't figure out if this should be the old or new
     -- clause body (i.e. relative to the positions of pattern variables or
     -- relative to the clauseTel). Both options pass the test suite, so I
     -- have the impression it doesn't actually matter.
     -- ALTERNATIVE CODE:
     -- perm = fromMaybe __IMPOSSIBLE__ $ IP.clausePerm cl
     -- body = applySubst (renamingR perm) $ I.clauseBody cl
        body = I.clauseBody cl
        pats = I.clausePats cl
    pats' <- mapM convert (IP.unnumberPatVars pats :: [Cm.Arg I.Pattern])
    body' <- traverse convert =<< lift (normalise body)
    return $ (pats',) <$> body'

instance Conversion TOM (Cm.Arg I.Pattern) (Pat O) where
  convert p = case Cm.unArg p of
    I.IApplyP _ _ _ n  -> return $ PatVar (prettyShow n)
    I.VarP _ n  -> return $ PatVar (prettyShow n)
    I.DotP _ _  -> return $ PatVar "_"
      -- because Agda includes these when referring to variables in the body
    I.ConP con _ pats -> do
      let n = I.conName con
      c     <- getConst True n TMAll
      pats' <- mapM (convert . fmap Cm.namedThing) pats
      def   <- lift $ getConstInfo n
      cc    <- lift $ liftIO $ readIORef c
      let Just (npar,_) = fst $ cdorigin cc
      return $ PatConApp c (replicate npar PatExp ++ pats')
    I.ProjP _ q -> PatProj <$> getConst True q TMAll

    -- UNSUPPORTED CASES
    I.LitP{}    -> lift literalsNotImplemented
    I.DefP{}    -> lift hitsNotImplemented

instance Conversion TOM I.Type (MExp O) where
  convert (I.El _ t) = convert t -- sort info is thrown away

instance Conversion TOM I.Term (MExp O) where
  convert v0 =
    case I.unSpine v0 of
      I.Var v es -> do
        let Just as = I.allApplyElims es
        as' <- convert as
        return $ NotM $ App Nothing (NotM OKVal) (Var v) as'
      I.Lam info b -> do
        b' <- convert (I.absBody b)
        return $ NotM $ Lam (getHiding info) (Abs (Id $ I.absName b) b')
      t@I.Lit{} -> do
        t <- lift $ constructorForm t
        case t of
          I.Lit{} -> lift literalsNotImplemented
          _       -> convert t
      I.Level l -> convert =<< lift (reallyUnLevelView l)
      I.Def name es -> do
        let Just as = I.allApplyElims es
        c   <- getConst False name TMAll
        as' <- convert as
        return $ NotM $ App Nothing (NotM OKVal) (Const c) as'
      I.Con con ci es -> do
        let Just as = I.allApplyElims es
        let name = I.conName con
        c   <- getConst True name TMAll
        as' <- convert as
        def <- lift $ getConstInfo name
        cc  <- lift $ liftIO $ readIORef c
        let Just (npar,_) = fst $ cdorigin cc
        return $ NotM $ App Nothing (NotM OKVal) (Const c) (foldl (\x _ -> NotM $ ALConPar x) as' [1..npar])
      I.Pi (I.Dom{domInfo = info, unDom = x}) b -> do
        let y    = I.absBody b
            name = I.absName b
        x' <- convert x
        y' <- convert y
        return $ NotM $ Pi Nothing (getHiding info) (Free.freeIn 0 y) x' (Abs (Id name) y')
      I.Sort (I.Type (I.ClosedLevel l)) -> return $ NotM $ Sort $ Set $ fromIntegral l
      I.Sort _ -> return $ NotM $ Sort UnknownSort
      I.Dummy{}-> return $ NotM $ Sort UnknownSort
      t@I.MetaV{} -> do
        t <- lift $ instantiate t
        case t of
          I.MetaV mid _ -> do
            mcurmeta <- gets sCurMeta
            case mcurmeta of
              Nothing -> return ()
              Just curmeta ->
                modify $ \ s -> s { sMetas = first (Map.adjust (\(m, x, deps) -> (m, x, mid : deps)) curmeta) (sMetas s) }
            m <- getMeta mid
            return $ Meta m
          _ -> convert t
      I.DontCare _ -> return $ NotM dontCare

instance Conversion TOM a b => Conversion TOM (Cm.Arg a) (Hiding, b) where
  convert (Cm.Arg info a) = (getHiding info,) <$> convert a

instance Conversion TOM I.Args (MM (ArgList O) (RefInfo O)) where
  convert as = NotM . foldr (\ (hid,t) -> ALCons hid t . NotM) ALNil
               <$> mapM convert as

tomyIneq :: MB.Comparison -> Bool
tomyIneq MB.CmpEq = False
tomyIneq MB.CmpLeq = True

-- ---------------------------------------------

fmType :: I.MetaId -> I.Type -> Bool
fmType m (I.El _ t) = fmExp m t

fmExp :: I.MetaId -> I.Term -> Bool
fmExp m (I.Var _ as) = fmExps m $ I.argsFromElims as
fmExp m (I.Lam _ b) = fmExp m (I.unAbs b)
fmExp m (I.Lit _) = False
fmExp m (I.Level (I.Max _ as)) = any (fmLevel m) as
fmExp m (I.Def _ as) = fmExps m $ I.argsFromElims as
fmExp m (I.Con _ ci as) = fmExps m $ I.argsFromElims as
fmExp m (I.Pi x y)  = fmType m (I.unDom x) || fmType m (I.unAbs y)
fmExp m (I.Sort _) = False
fmExp m (I.MetaV mid _) = mid == m
fmExp m (I.DontCare _) = False
fmExp _ I.Dummy{} = False

fmExps :: I.MetaId -> I.Args -> Bool
fmExps m as = any (fmExp m . Cm.unArg) as

fmLevel :: I.MetaId -> I.PlusLevel -> Bool
fmLevel m (I.Plus _ l) = fmExp m l

-- ---------------------------------------------

icnvh :: Hiding -> Cm.ArgInfo
icnvh h = Cm.setHiding h $
          Cm.setOrigin o $
          Cm.defaultArgInfo
    where
    -- Andreas, 2017-01-18, issue #819.
    -- Visible arguments are made UserWritten,
    -- otherwise they might not be printed in patterns.
    o = case h of
          NotHidden  -> Cm.UserWritten
          Instance{} -> Cm.Inserted
          Hidden     -> Cm.Inserted

-- ---------------------------------------------

instance Conversion MOT a b => Conversion MOT (MM a (RefInfo O)) b where
  convert meta = case meta of
    NotM a -> convert a
    Meta m -> do
      ma <- lift $ readIORef $ mbind m
      case ma of
        Nothing -> throwError "meta not bound"
        Just a  -> convert a

instance Conversion MOT a b => Conversion MOT (Abs a) (I.Abs b) where
  convert (Abs mid t) = I.Abs id <$> convert t where
    id = case mid of
           NoId  -> "x"
           Id id -> id

instance Conversion MOT (Exp O) I.Type where
  convert e = I.El (I.mkType 0) <$> convert e
              -- 0 is arbitrary, sort not read by Agda when reifying

instance Conversion MOT (Exp O) I.Term where
  convert = \case
    App _ _ (Var v) as -> frommyExps 0 as (I.Var v [])
    App _ _ (Const c) as -> do
      cdef <- lift $ readIORef c
      let (iscon, name) = cdorigin cdef
{-
   case iscon of
      Just n -> do
        v <- getConTerm name -- We are not in TCM
        frommyExps n as v
-}
          (ndrop, h) = case iscon of
                         Just (n,fs) -> (n, \ q -> I.Con (I.ConHead q I.IsData Cm.Inductive fs) Cm.ConOSystem)
                         Nothing -> (0, \ f vs -> I.Def f vs)
      frommyExps ndrop as (h name [])
    Lam hid t -> I.Lam (icnvh hid) <$> convert t
    Pi _ hid _ x y -> do
      x' <- convert x
      let dom = (I.defaultDom x') {domInfo = icnvh hid}
      I.Pi dom <$> convert y
   -- maybe have case for Pi where possdep is False which produces Fun (and has to unweaken y), return $ I.Fun (Cm.Arg (icnvh hid) x') y'
    Sort (Set l) -> return $ I.Sort (I.mkType (fromIntegral l))
    Sort Type -> __IMPOSSIBLE__
    Sort UnknownSort -> return $ I.Sort (I.mkType 0) -- hoping it's thrown away

    AbsurdLambda hid -> return $ I.Lam (icnvh hid)
                               $ I.Abs abslamvarname (I.Var 0 [])

frommyExps :: Nat -> MArgList O -> I.Term -> ExceptT String IO I.Term
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
   x' <- convert x
   frommyExps ndrop xs (addend (Cm.Arg (icnvh hid) x') trm)

  -- Andreas, 2013-10-19 TODO: restore postfix projections
  ALProj eas idx hid xs -> do
   idx <- lift $ expandbind idx
   c <- case idx of
            NotM c -> return c
            Meta{} -> throwError "meta not bound"
   cdef <- lift $ readIORef c
   let name = snd $ cdorigin cdef
   trm2 <- frommyExps 0 eas (I.Def name [])
   frommyExps 0 xs (addend (Cm.Arg (icnvh hid) trm) trm2)

  ALConPar xs | ndrop > 0 -> frommyExps (ndrop - 1) xs trm
  ALConPar _ -> __IMPOSSIBLE__
 where
  addend x (I.Var h xs) = I.Var h (xs ++ [I.Apply x])
  addend x (I.Con h ci xs) = I.Con h ci (xs ++ [I.Apply x])
  addend x (I.Def h xs) = I.Def h (xs ++ [I.Apply x])
  addend _ _ = __IMPOSSIBLE__

-- --------------------------------

abslamvarname :: String
abslamvarname = "\0absurdlambda"

modifyAbstractExpr :: A.Expr -> A.Expr
modifyAbstractExpr = f
 where
  f (A.App i e1 (Cm.Arg info (Cm.Named n e2))) =
        A.App i (f e1) (Cm.Arg info (Cm.Named n (f e2)))
  f (A.Lam i (A.DomainFree _ x) _)
     | A.Binder _ (A.BindName{unBind = n}) <- Cm.namedArg x
     , prettyShow (A.nameConcrete n) == abslamvarname =
        A.AbsurdLam i $ Cm.getHiding x
  f (A.Lam i b e) = A.Lam i b (f e)
  f (A.Rec i xs) = A.Rec i (map (mapLeft (over exprFieldA f)) xs)
  f (A.RecUpdate i e xs) = A.RecUpdate i (f e) (map (over exprFieldA f) xs)
  f (A.ScopedExpr i e) = A.ScopedExpr i (f e)
  f e = e

modifyAbstractClause :: A.Clause -> A.Clause
modifyAbstractClause (A.Clause lhs spats (A.RHS e mc) decls catchall) =
  A.Clause lhs spats (A.RHS (modifyAbstractExpr e) mc) decls catchall
modifyAbstractClause cl = cl

-- ---------------------------------


constructPats :: Map AN.QName (TMode, ConstRef O) -> I.MetaId -> I.Clause -> MB.TCM ([(Hiding, MId)], [CSPat O])
constructPats cmap mainm clause = do
 let cnvps ns [] = return (ns, [])
     cnvps ns (p : ps) = do
      (ns', ps') <- cnvps ns ps
      (ns'', p') <- cnvp ns' p
      return (ns'', p' : ps')
     cnvp ns p =
      let hid = getHiding $ Cm.argInfo p
      in case Cm.namedArg p of
       I.VarP _ n -> return ((hid, Id n) : ns, HI hid (CSPatVar $ length ns))
       I.IApplyP _ _ _ n -> return ((hid, Id n) : ns, HI hid (CSPatVar $ length ns))
       I.ConP con _ ps -> do
        let c = I.conName con
        (c2, _) <- runStateT (getConst True c TMAll) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing, sMainMeta = mainm})
        (ns', ps') <- cnvps ns ps
        cc <- liftIO $ readIORef c2
        let Just (npar,_) = fst $ cdorigin cc
        return (ns', HI hid (CSPatConApp c2 (replicate npar (HI Hidden CSOmittedArg) ++ ps')))
       I.DotP _ t -> do
        (t2, _) <- runStateT (convert t) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing, sMainMeta = mainm})
        return (ns, HI hid (CSPatExp t2))
       I.ProjP po c -> do
        (c2, _) <- runStateT (getConst True c TMAll) (S {sConsts = (cmap, []), sMetas = initMapS, sEqs = initMapS, sCurMeta = Nothing, sMainMeta = mainm})
        cc <- liftIO $ readIORef c2
        return (ns, HI hid (CSPatProj c2))
       I.LitP{} -> literalsNotImplemented
       I.DefP{} -> hitsNotImplemented

 (names, pats) <- cnvps [] (IP.unnumberPatVars $ I.namedClausePats clause)
 return (reverse names, pats)


frommyClause :: (CSCtx O, [CSPat O], Maybe (MExp O)) -> ExceptT String IO I.Clause
frommyClause (ids, pats, mrhs) = do
 let ctel [] = return I.EmptyTel
     ctel (HI hid (mid, t) : ctx) = do
      let Id id = mid
      tel <- ctel ctx
      t' <- convert t
      let dom = (I.defaultDom t') {domInfo = icnvh hid}
      return $ I.ExtendTel dom (I.Abs id tel)
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
        let (Just (ndrop,_), _) = cdorigin cdef
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
       CSPatVar v -> return (I.varP $ let HI _ (Id n, _) = ids !! v in n)
       CSPatConApp c ps -> do
        cdef <- lift $ readIORef c
        let (Just (ndrop,_), name) = cdorigin cdef
        ps' <- cnvps ndrop ps
        let con = I.ConHead name I.IsData Cm.Inductive [] -- TODO: restore DataOrRecord and record fields!
        return (I.ConP con I.noConPatternInfo ps')
       CSPatExp e -> do
        e' <- convert e {- renm e -} -- renaming before adding to clause below
        return (I.dotP e')
       CSAbsurd -> __IMPOSSIBLE__ -- CSAbsurd not used
       _ -> __IMPOSSIBLE__
      return $ Cm.Arg (icnvh hid) $ Cm.unnamed p'   -- TODO: recover names
 ps <- cnvps 0 pats
 body <- case mrhs of
          Nothing -> return $ Nothing
          Just e -> Just <$> convert e
 let cperm =  Perm nv perm
 return $ I.Clause
   { I.clauseLHSRange  = SP.noRange
   , I.clauseFullRange = SP.noRange
   , I.clauseTel       = tel
   , I.namedClausePats = IP.numberPatVars __IMPOSSIBLE__ cperm $ applySubst (renamingR $ compactP cperm) ps
   , I.clauseBody  = body
   , I.clauseType  = Nothing -- TODO: compute clause type
   , I.clauseCatchall = False
   , I.clauseExact       = Nothing -- TODO
   , I.clauseRecursive   = Nothing -- TODO: Don't know here whether recursive or not !?
   , I.clauseUnreachable = Nothing -- TODO: Don't know here whether reachable or not !?
   , I.clauseEllipsis = Cm.NoEllipsis
   }

contains_constructor :: [CSPat O] -> Bool
contains_constructor = any f
 where
  f (HI _ p) = case p of
         CSPatConApp{} -> True
         _ -> False

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
negtype ee = f (0 :: Int)
 where
  mr x = let NotM x' = x in x'
  f n e = case mr e of
   Pi uid hid possdep it (Abs id ot) -> NotM $ Pi uid hid possdep it (Abs id (f (n + 1) ot))
   _ -> NotM $ Pi Nothing NotHidden False (NotM $ Pi Nothing NotHidden False e (Abs NoId (NotM $ Pi Nothing NotHidden True (NotM $ Sort (Set 0)) (Abs NoId (NotM $ App Nothing (NotM OKVal) (Var 0) (NotM ALNil)))))) (Abs NoId (NotM $ App Nothing (NotM OKVal) (Const ee) (NotM ALNil)))

-- ---------------------------------------

findClauseDeep :: Cm.InteractionId -> MB.TCM (Maybe (AN.QName, I.Clause, Bool))
findClauseDeep ii = ignoreAbstractMode $ do  -- Andreas, 2016-09-04, issue #2162
  MB.InteractionPoint { MB.ipClause = ipCl} <- lookupInteractionPoint ii
  case ipCl of
    MB.IPNoClause -> return Nothing
    MB.IPClause f clauseNo _ _ _ _ _ -> do
      (_, (_, c, _)) <- getClauseZipperForIP f clauseNo
      return $ Just (f, c, maybe __IMPOSSIBLE__ toplevel $ I.clauseBody c)
  where
    toplevel e =
     case e of
      I.MetaV{} -> True
      _ -> False

-- ---------------------------------------

matchType :: Int -> Int -> I.Type -> I.Type -> Maybe (Nat, Nat) -- Nat is deffreevars of const, Nat is ctx length of target type, left arg is const type, right is target type
matchType cdfv tctx ctyp ttyp = trmodps cdfv ctyp
 where
  trmodps 0 ctyp = tr 0 0 ctyp
  trmodps n ctyp = case I.unEl ctyp of
   I.Pi _ ot -> trmodps (n - 1) (I.absBody ot)
   _ -> __IMPOSSIBLE__
  tr narg na ctyp =
   case ft 0 0 Just ctyp ttyp of
    Just n -> Just (n, narg)
    Nothing -> case I.unEl ctyp of
     I.Pi _ (I.Abs _ ot) -> tr (narg + 1) (na + 1) ot
     I.Pi _ (I.NoAbs _ ot) -> tr (narg + 1) na ot
     _ -> Nothing
   where
    ft nl n c (I.El _ e1) (I.El _ e2) = f nl n c e1 e2
    f nl n c e1 e2 = case e1 of
     I.Var v1 as1 | v1 < nl -> case e2 of
      I.Var v2 as2 | v1 == v2 -> fes nl (n + 1) c as1 as2
      _ -> Nothing
     I.Var v1 _ | v1 < nl + na -> c n -- unify vars with no args?
     I.Var v1 as1 -> case e2 of
      I.Var v2 as2 | cdfv + na + nl - v1 == tctx + nl - v2 -> fes nl (n + 1) c as1 as2
      _ -> Nothing
     _ -> case (e1, e2) of
      (I.MetaV{}, _) -> c n
      (_, I.MetaV{}) -> c n
      (I.Lam hid1 b1, I.Lam hid2 b2) | hid1 == hid2 -> f (nl + 1) n c (I.absBody b1) (I.absBody b2)
      (I.Lit lit1, I.Lit lit2) | lit1 == lit2 -> c (n + 1)
      (I.Def n1 as1, I.Def n2 as2) | n1 == n2 -> fes nl (n + 1) c as1 as2
      (I.Con n1 _ as1, I.Con n2 _ as2) | n1 == n2 -> fs nl (n + 1) c as1 as2
      (I.Pi (I.Dom{domInfo = info1, unDom = it1})  ot1, I.Pi (I.Dom{domInfo = info2, unDom = it2})  ot2) | Cm.argInfoHiding info1 == Cm.argInfoHiding info2 -> ft nl n (\n -> ft (nl + 1) n c (I.absBody ot1) (I.absBody ot2)) it1 it2
      (I.Sort{}, I.Sort{}) -> c n -- sloppy
      _ -> Nothing
    fs nl n c es1 es2 = case (es1, es2) of
     ([], []) -> c n
     (I.Apply (Cm.Arg info1 e1) : es1, I.Apply (Cm.Arg info2 e2) : es2) | Cm.argInfoHiding info1 == Cm.argInfoHiding info2 -> f nl n (\n -> fs nl n c es1 es2) e1 e2
     _ -> Nothing
    fes nl n c es1 es2 = case (es1, es2) of
     ([], []) -> c n
     (I.Proj _ f : es1, I.Proj _ f' : es2) | f == f' -> fes nl n c es1 es2
     (I.Apply (Cm.Arg info1 e1) : es1, I.Apply (Cm.Arg info2 e2) : es2) | Cm.argInfoHiding info1 == Cm.argInfoHiding info2 -> f nl n (\n -> fes nl n c es1 es2) e1 e2
     _ -> Nothing
