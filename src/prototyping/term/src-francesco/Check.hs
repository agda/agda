{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Check where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>))
import           Debug.Trace                      (trace)

import           Data.Void                        (vacuous)
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Syntax.Abstract                  as A
import           Types.Definition
import qualified Types.Context                    as Ctx
import qualified Types.Telescope                  as Tel
import           Types.Monad
import           Types.Term
import           Text.PrettyPrint.Extended        (render)
import qualified Text.PrettyPrint.Extended        as PP

-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: (DeBruijn v, Eq v) => A.Expr -> Type v -> TC v (Term v)
check synT type_ = atSrcLoc synT $ case synT of
  A.App (A.Con dataCon) synArgs -> do
    dataConDef <- getDefinition dataCon
    case dataConDef of
      Constructor _ tyCon dataConType -> do
        typeView <- whnfView type_
        case typeView of
          App (Def tyCon') args0
            | tyCon == tyCon', Just args <- mapM isApply args0 -> do
              let appliedDataConType = Tel.substs (vacuous dataConType) args
              fst <$> checkSpine (con dataCon) synArgs appliedDataConType
          _ -> typeError $ "1 Constructor type error " ++ render synT ++ " : " ++ render typeView
      _ -> typeError $ "2 Constructor type error " ++ render synT ++ " : " ++ render type_
  A.App (A.Refl _) args@(_ : _) ->
    typeError $ "Type error: refl applied to arguments: refl " ++ render args
  A.App (A.Refl _) [] -> do
    typeView <- whnfView type_
    case typeView of
      Equal type' x y -> do
        checkEqual type' x y
        return refl
      _ ->
          typeError $ render typeView ++
                      " is (perhaps) not an application of the equality type"
  A.Meta _ ->
    addFreshMetaVar type_
  A.Lam name synBody -> do
    typeView <- whnfView type_
    case typeView of
      Pi domain codomain -> do
         body <- extendContext name domain $ \_ _ ->
           check synBody (fromAbs codomain)
         return $ lam (toAbs body)
      App (Meta _) _ ->
        error "TODO check Meta Lam"
      _ ->
        typeError $ "Lambda type error " ++ render synT ++ " : " ++ render typeView
  _ -> do
    (t, type') <- infer synT
    equalType type_ type'
    return t

checkSpine :: (DeBruijn v, Eq v)
           => Term v -> [A.Elim] -> Type v -> TC v (Term v, Type v)
checkSpine h []         type_ = return (h, type_)
checkSpine h (el : els) type_ = atSrcLoc el $ case el of
  A.Proj proj -> do
    (h', type') <- applyProjection proj h type_
    checkSpine h' els type'
  A.Apply synArg -> do
    typeView <- whnfView type_
    case typeView of
      Pi domain codomain -> do
        arg <- check synArg domain
        let codomain' = instantiate codomain arg
        let h' = eliminate h [Apply arg]
        checkSpine h' els codomain'
      _ ->
        typeError $ "Expected function type " ++ render typeView ++
                    "\n  in application of " ++ render synArg

infer :: (DeBruijn v, Eq v) => A.Expr -> TC v (Term v, Type v)
infer synT = atSrcLoc synT $ case synT of
  A.Set _ ->
    return (set, set)
  A.Pi name synDomain synCodomain -> do
    domain   <- isType synDomain
    codomain <- extendContext name domain $ \_ _ -> isType synCodomain
    return (pi domain (toAbs codomain), set)
  A.Fun synDomain synCodomain -> do
    domain   <- isType synDomain
    codomain <- isType synCodomain
    return (pi domain (weaken codomain), set)
  A.App synH elims -> do
    (h, type_) <- inferHead synH
    (t, type') <- checkSpine (unview (App h [])) elims type_
    return (t, type')
  A.Equal synType synX synY -> do
    type_ <- isType synType
    x <- check synX type_
    y <- check synY type_
    return (equal type_ x y, set)
  _ -> error "TODO infer"

inferHead :: (DeBruijn v, Eq v) => A.Head -> TC v (Head v, Type v)
inferHead synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    (v, type_) <- getTypeOfName name
    return (Var v, type_)
  A.Def name -> do
    type_ <- definitionType <$> getDefinition name
    return (Def name, vacuous type_)
  A.J{} ->
    error "TODO inferHead J"
  A.Con{} ->
    typeError $ "Cannot infer type of application of constructor " ++ render synH
  A.Refl{} ->
    typeError $ "Cannot infer type of refl"

-- Equality
-----------

checkEqual :: (DeBruijn v, Eq v) => Type v -> Term v -> Term v -> TC v ()
checkEqual _ x y | x == y =
  return ()
checkEqual type_ x y = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      let codomain' = fromAbs codomain
      extendContext (absName codomain') domain $ \v ctxV -> do
        let v' = var v
        let x' = eliminate (fmap (Ctx.weaken ctxV) x) [Apply v']
        let y' = eliminate (fmap (Ctx.weaken ctxV) y) [Apply v']
        checkEqual codomain' x' y'
    _ ->
      inferEqual x y

inferEqual :: (DeBruijn v, Eq v) => Term v -> Term v -> TC v ()
inferEqual x y = do
  xView <- whnfView x
  yView <- whnfView y
  case (xView, yView) of
    (App (Meta _) _, _) ->
      error "TODO inferEqual meta"
    (_, App (Meta _) _) ->
      error "TODO inferEqual meta"
    (App h1 elims1, App h2 elims2) | h1 == h2 -> do
      h1Type <- case h1 of
        Var v   -> getTypeOfVar v
        Def f   -> vacuous . definitionType <$> getDefinition f
        Con c   -> vacuous . definitionType <$> getDefinition c
        J       -> error "TODO typeOfJ"
        Refl    -> error "TODO typeOfRefl"
        Meta mv -> vacuous <$> getTypeOfMetaVar mv
      equalSpine h1Type (unview (App h1 [])) elims1 elims2
    _ ->
      typeError $ render xView ++ " != " ++ render yView

equalSpine
    :: (DeBruijn v, Eq v)
    => Type v
    -- ^ Type of the head.
    -> Term v
    -- ^ Head.
    -> [Elim Term v] -> [Elim Term v] -> TC v ()
equalSpine _ _ [] [] =
  return ()
equalSpine type_ h (Apply arg1 : elims1) (Apply arg2 : elims2) = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      checkEqual domain arg1 arg2
      equalSpine (instantiate codomain arg1) (eliminate h [Apply arg1]) elims1 elims2
    _ ->
      error $ "Expected function type " ++ render typeView
equalSpine type_ h (Proj proj projIx : elims1) (Proj proj' projIx' : elims2)
  | proj == proj' && projIx == projIx' = do
    (h', type') <- applyProjection proj h type_
    equalSpine type' h' elims1 elims2
equalSpine type_ _ elims1 elims2 =
  typeError $ render elims1 ++ " != " ++ render elims2 ++ " : " ++ render type_

applyProjection
    :: (DeBruijn v, Eq v)
    => Name
    -- ^ Name of the projection
    -> Term v
    -- ^ Head
    -> Type v
    -- ^ Type of the head
    -> TC v (Term v, Type v)
applyProjection proj h type_ = do
  projDef <- getDefinition proj
  case projDef of
    Projection _ projIx tyCon projType -> do
      typeView <- whnfView type_
      case typeView of
        App (Def tyCon') tyConArgs0
          | tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 -> do
            let appliedProjType = view $ Tel.substs (vacuous projType) tyConArgs
            case appliedProjType of
              Pi _ endType -> do
                let endType' = instantiate endType h
                let h' = eliminate h [Proj proj projIx]
                return (h', endType')
              _ ->
                error $ "impossible.applyProjection: " ++ render appliedProjType
        App (Meta _) _ ->
          error "TODO applyProjection App (Meta mv) els"
        _ ->
          typeError $ render typeView ++ " is not a record type"
    _ ->
      error $ "impossible.applyProjection: " ++ render projDef

-- Checking definitions
------------------------------------------------------------------------

checkProgram :: [A.Decl] -> ClosedTC ()
checkProgram = mapM_ checkDecl

checkDecl :: A.Decl -> ClosedTC ()
checkDecl decl = atSrcLoc decl $ do
  trace (render decl) $ return ()
  case decl of
    A.TypeSig sig      -> checkTypeSig sig
    A.DataDef d xs cs  -> checkData d xs cs
    A.RecDef d xs c fs -> checkRec d xs c fs
    A.FunDef f ps b    -> checkClause f ps b

checkTypeSig :: A.TypeSig -> ClosedTC ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType absType
    addConstant name Postulate type_

-- Data
-------

checkData
    :: Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> ClosedTC ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon Data tyConType
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        equalType endType set
        -- TODO maybe we should expose a 'vars' function from the Ctx
        -- and do the application ourselves.
        let appliedTyConType = ctxApp (def tyCon) tyConPars'
        mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: (DeBruijn v, Eq v)
    => Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx Type v
    -- ^ Ctx with the parameters of the tycon.
    -> Type v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC v ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) = do
    atSrcLoc dataCon $ do
        dataConType <- isType synDataConType
        unrollPi dataConType $ \vs endType -> do
            let appliedTyConType' = fmap (Ctx.weaken vs) appliedTyConType
            equalType appliedTyConType' endType
        addConstructor dataCon tyCon (Tel.idTel tyConPars dataConType)

-- Record
---------

checkRec
    :: Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [A.TypeSig]
    -- ^ Fields of the record.
    -> ClosedTC ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType <$> getDefinition tyCon
    addConstant tyCon Record tyConType
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        equalType endType set
        fieldsTel <- checkFields fields
        let appliedTyConType = ctxApp (def tyCon) tyConPars'
        extendContext (A.name "_") appliedTyConType $ \self selfCtx -> do
            addProjections
                tyCon tyConPars' self (map A.typeSigName fields) $
                (fmap (Ctx.weaken selfCtx) fieldsTel)
        addConstructor dataCon tyCon (Tel.idTel tyConPars' appliedTyConType)

checkFields
    :: (DeBruijn v, Eq v) => [A.TypeSig] -> TC v (Tel.ProxyTel Type v)
checkFields = go Ctx.Empty
  where
    go :: (DeBruijn v, DeBruijn v', Eq v, Eq v')
       => Ctx.Ctx v Type v' -> [A.TypeSig] -> TC v' (Tel.ProxyTel Type v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        extendContext field fieldType $ \_ _ ->
            go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: forall v.
       (DeBruijn v, Eq v)
    => Name
    -- ^ Type constructor.
    -> Ctx.ClosedCtx Type v
    -- ^ A context with the parameters to the type constructor.
    -> TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.ProxyTel Type (TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> TC (TermVar v) ()
addProjections tyCon tyConPars self fields0 =
    go $ zip fields0 $ map Field [1..]
  where
    go fields fieldTypes = case (fields, fieldTypes) of
        ([], Tel.Empty Tel.Proxy2) ->
            return ()
        ((field, ix) : fields', Tel.Cons (_, fieldType) fieldTypes') -> do
            let endType = pi (ctxApp (def tyCon) tyConPars) (toAbs fieldType)
            addProjection field ix tyCon (Tel.idTel tyConPars endType)
            go fields' $
                Tel.instantiate fieldTypes' $ unview $ App (Var self) [Proj tyCon ix]
        (_, _) -> error "addProjections: impossible: lengths do not match"

-- Clause
---------

-- TODO what about pattern coverage?

checkClause :: Name -> [A.Pattern] -> A.Expr -> ClosedTC ()
checkClause fun synPats synClauseBody = do
    funType <- definitionType <$> getDefinition fun
    checkPatterns synPats funType $ \_ pats _ clauseType -> do
        clauseBody <- check synClauseBody clauseType
        addClause fun pats =<< closeClauseBody clauseBody

checkPatterns
    :: (DeBruijn v, Eq v)
    => [A.Pattern]
    -> Type v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (forall v'. (DeBruijn v', Eq v') => (v -> v') -> [Pattern] -> [Term v'] -> Type v' -> TC v' a)
    -- ^ Handler taking a function to weaken an external variable,
    -- list of internal patterns, a list of terms produced by them, and
    -- the type of the clause body (scoped over the pattern variables).
    -> TC v a
checkPatterns [] type_ ret =
    ret id [] [] type_
checkPatterns (synPat : synPats) type0 ret = atSrcLoc synPat $ do
    typeView <- whnfView type0
    case typeView of
      Pi domain codomain ->
        checkPattern synPat domain $ \weaken_ pat patVar -> do
          let codomain'  = fmap weaken_ codomain
          let codomain'' = instantiate codomain' patVar
          checkPatterns synPats codomain'' $ \weaken_' pats patsVars -> do
            let patVar' = fmap weaken_' patVar
            ret (weaken_' . weaken_) (pat : pats) (patVar' : patsVars)
      _ ->
        typeError $ "Expected function type: " ++ render typeView

checkPattern
    :: (DeBruijn v, Eq v)
    => A.Pattern
    -> Type v
    -- ^ Type of the matched thing.
    -> (forall v'. (DeBruijn v', Eq v') => (v -> v') -> Pattern -> Term v' -> TC v' a)
    -- ^ Handler taking a weakening function, the internal 'Pattern',
    -- and a 'Term' containing the term produced by it.
    -> TC v a
checkPattern synPat type_ ret = case synPat of
    A.VarP name ->
      extendContext name type_ $ \v ctxV ->
      ret (Ctx.weaken ctxV) VarP (var v)
    A.WildP _ ->
      extendContext (A.name "_") type_ $ \v ctxV ->
      ret (Ctx.weaken ctxV) VarP (var v)
    A.ConP dataCon synPats -> do
      dataConDef <- getDefinition dataCon
      case dataConDef of
        Constructor _ typeCon dataConType -> do
          typeConDef <- getDefinition typeCon
          case typeConDef of
            Constant _ Data   _ -> return ()
            Constant _ Record _ -> typeError $ "Pattern matching is not supported " ++
                                               "for the record constructor " ++ render dataCon
            _                   -> error $ "checkPattern: impossible" ++ render dataConDef
          typeView <- whnfView type_
          case typeView of
            App (Def typeCon') typeConPars0
              | typeCon == typeCon', Just typeConPars <- mapM isApply typeConPars0 -> do
                let dataConTypeNoPars =
                        Tel.substs (vacuous dataConType) typeConPars
                checkPatterns synPats dataConTypeNoPars $ \weaken_ pats patsVars _ -> do
                  let t = unview (App (Con dataCon) $ map Apply patsVars)
                  ret weaken_ (ConP dataCon pats) t
            _ ->
              typeError $ render dataCon ++
                            " does not construct an element of " ++ render type_
        _ ->
          typeError $ "Should be constructor: " ++ render dataCon

-- Utils
------------------------------------------------------------------------

equalType :: (DeBruijn v, Eq v) => Type v -> Type v -> TC v ()
equalType a b = checkEqual set a b

isApply :: (DeBruijn v, Eq v) => Elim Term v -> Maybe (Term v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isType :: (DeBruijn v, Eq v) => A.Expr -> TC v (Type v)
isType abs = check abs set

definitionType :: Definition Term -> Closed Type
definitionType (Constant _ _ type_)   = type_
definitionType (Constructor _ _ tel)  = telPi tel
definitionType (Projection _ _ _ tel) = telPi tel
definitionType (Function _ type_ _)   = type_

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
    :: (DeBruijn v, Eq v)
    => Type v
    -- ^ Type to unroll
    -> [Name]
    -- ^ Names to give to each parameter
    -> (forall v'. (DeBruijn v', Eq v') => Ctx.Ctx v Type v' -> Type v' -> TC v' a)
    -- ^ Handler taking a context with accumulated domains of the pis
    -- and the final codomain.
    -> TC v a
unrollPiWithNames type_ []             ret = ret Ctx.Empty type_
unrollPiWithNames type_ (name : names) ret = do
    typeView <- whnfView type_
    case typeView of
        Pi domain codomain ->
            extendContext name domain $ \_v ctxV ->
            unrollPiWithNames (fromAbs codomain) names $ \ctxVs endType ->
            ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            typeError $ "Expected function type: " ++ render typeView

unrollPi
    :: (DeBruijn v, Eq v)
    => Type v
    -- ^ Type to unroll
    -> (forall v'. (DeBruijn v', Eq v') => Ctx.Ctx v Type v' -> Type v' -> TC v' a)
    -- ^ Handler taking a weakening function, the list of domains
    -- of the unrolled pis, the final codomain.
    -> TC v a
unrollPi type_ ret = do
    typeView <- whnfView type_
    case typeView of
        Pi domain codomain -> do
            let codomain' = fromAbs codomain
            extendContext (absName codomain') domain $ \_v ctxV ->
                unrollPi codomain' $ \ctxVs endType ->
                ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            ret Ctx.Empty type_

-- Monad utils
--------------

addConstant :: (DeBruijn v, Eq v) => Name -> ConstantKind -> Closed Type -> TC v ()
addConstant x k a = addDefinition x (Constant x k a)

addConstructor :: (DeBruijn v, Eq v) => Name -> Name -> Tel.ClosedIdTel Type -> TC v ()
addConstructor c d tel = addDefinition c (Constructor c d tel)

addProjection :: (DeBruijn v, Eq v) => Name -> Field -> Name -> Tel.ClosedIdTel Type -> TC v ()
addProjection f n r tel = addDefinition f (Projection f n r tel)

addClause :: (DeBruijn v, Eq v) => Name -> [Pattern] -> ClauseBody Term -> TC v ()
addClause f ps v = do
  def' <- getDefinition f
  let ext (Constant x Postulate a) = Function x a [c]
      ext (Function x a cs)        = Function x a (cs ++ [c])
      ext (Constant _ k _)         = error $ "Monad.addClause " ++ render k
      ext Constructor{}            = error $ "Monad.addClause constructor"
      ext Projection{}             = error $ "Monad.addClause projection"
  addDefinition f (ext def')
  where
    c = Clause ps v

-- Telescope utils
------------------

telPi :: (DeBruijn v, Eq v) => Tel.IdTel Term v -> Term v
telPi tel = Tel.unTel tel $ \ctx endType -> ctxPi ctx (Tel.unId2 endType)
