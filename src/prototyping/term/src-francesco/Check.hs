{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Check where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>))

import           Data.Void                        (vacuous)
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Syntax.Abstract                  as A
import           Types.Definition
import qualified Types.Context                    as Ctx
import qualified Types.Telescope                  as Tel
import           Types.Monad
import           Types.Term

-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: A.Expr -> Type v -> TC v (Term v)
check = undefined
-- check synT type_ = I.atSrcLoc synT $ case synT of
--   A.App (A.Con dataCon) synArgs -> do
--     dataConDef <- getDefinition dataCon
--     case dataConDef of
--       Constructor _ tyCon dataConType -> do
--         synType <- whnfView type_
--         case synType of
--           App (Def dataCon') args0
--             | dataCon == dataCon', Just args <- mapM isApply args0 -> do
--               let appliedDataConType = I.Ctx.instantiate dataConType args
--               let h = I.unview (App (Con dataCon) [])
--               checkSpine h synArgs

infer :: A.Expr -> TC v (Term v, Type v)
infer = undefined

-- Equality
-----------

checkEqual :: Type v -> Term v -> Term v -> TC v ()
checkEqual = undefined

inferEqual :: Term v -> Term v -> TC v ()
inferEqual = undefined

-- Checking definitions
------------------------------------------------------------------------

checkDecl :: A.Decl -> ClosedTC ()
checkDecl = undefined

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
    :: Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx Type v
    -- ^ Ctx with the parameters of the tycon.
    -> Type v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC v ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) =
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
    :: [A.TypeSig]
    -> TC v (Tel.ProxyTel Type v)
checkFields = go Ctx.Empty
  where
    go :: Ctx.Ctx v Type v' -> [A.TypeSig] -> TC v' (Tel.ProxyTel Type v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        extendContext field fieldType $ \_ _ ->
            go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: forall v.
       Name
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
                Tel.instantiate fieldTypes' $ unview $ App (Var self) [Proj ix]
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
    :: [A.Pattern]
    -> Type v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (forall v'. (v -> v') -> [Pattern] -> [Term v'] -> Type v' -> TC v' a)
    -- ^ Handler taking a function to weaken an external variable,
    -- list of internal patterns, a list of terms produced by them, and
    -- the type of the clause body (scoped over the pattern variables).
    -> TC v a
checkPatterns [] type_ ret =
    ret id [] [] type_
checkPatterns (synPat : synPats) type0 ret = atSrcLoc synPat $ do
    type_ <- whnfView type0
    case type_ of
      Pi domain codomain ->
        checkPattern synPat domain $ \weaken pat patVar -> do
          let codomain'  = fmap weaken codomain
          let codomain'' = instantiate codomain' patVar
          checkPatterns synPats codomain'' $ \weaken' pats patsVars -> do
            let patVar' = fmap weaken' patVar
            ret (weaken' . weaken) (pat : pats) (patVar' : patsVars)
      _ ->
        typeError $ "Expected function type: " ++ error "TODO show type_"

checkPattern
    :: A.Pattern
    -> Type v
    -- ^ Type of the matched thing.
    -> (forall v'. (v -> v') -> Pattern -> Term v' -> TC v' a)
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
                                                "for the record constructor " ++ show dataCon
            _                   -> typeError $ "checkPattern: impossible" ++ error "TODO show def"
          synType <- whnfView type_
          case synType of
            App (Def typeCon') typeConPars0
              | typeCon == typeCon', Just typeConPars <- mapM isApply typeConPars0 -> do
                let dataConTypeNoPars =
                        Tel.unId2 $ Tel.substs (vacuous dataConType) typeConPars
                checkPatterns synPats dataConTypeNoPars $ \weaken pats patsVars _ -> do
                  let t = unview (App (Con dataCon) $ map Apply patsVars)
                  ret weaken (ConP dataCon pats) t
            _ ->
              typeError $ show dataCon ++
                            " does not construct an element of " ++ error "TODO show type_"
        _ ->
          typeError $ "Should be constructor: " ++ show dataCon

-- Utils
------------------------------------------------------------------------

equalType :: Type v -> Type v -> TC v ()
equalType a b = checkEqual set a b

isApply :: Elim Term v -> Maybe (Term v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isType :: A.Expr -> TC v (Type v)
isType abs = check abs set

definitionType :: Definition Term -> Closed Type
definitionType = undefined

absName :: Term (TermVar v) -> Name
absName = undefined

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
    :: Type v
    -- ^ Type to unroll
    -> [Name]
    -- ^ Names to give to each parameter
    -> (forall v'. Ctx.Ctx v Type v' -> Type v' -> TC v' a)
    -- ^ Handler taking a context with accumulated domains of the pis
    -- and the final codomain.
    -> TC v a
unrollPiWithNames type_ []             ret = ret Ctx.Empty type_
unrollPiWithNames type_ (name : names) ret = do
    synType <- whnfView type_
    case synType of
        Pi domain codomain ->
            extendContext name domain $ \_v ctxV ->
            unrollPiWithNames (fromAbs codomain) names $ \ctxVs endType ->
            ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            typeError $ "Expected function type: " ++ error "TODO show synType"

unrollPi
    :: Type v
    -- ^ Type to unroll
    -> (forall v'. Ctx.Ctx v Type v' -> Type v' -> TC v' a)
    -- ^ Handler taking a weakening function, the list of domains
    -- of the unrolled pis, the final codomain.
    -> TC v a
unrollPi type_ ret = do
    synType <- whnfView type_
    case synType of
        Pi domain codomain -> do
            let codomain' = fromAbs codomain
            extendContext (absName codomain') domain $ \_v ctxV ->
                unrollPi codomain' $ \ctxVs endType ->
                ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            ret Ctx.Empty type_

-- Monad utils
--------------

addConstant :: Name -> ConstantKind -> Closed Type -> TC v ()
addConstant x k a = addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> Tel.ClosedIdTel Type -> TC v ()
addConstructor c d tel = addDefinition c (Constructor c d tel)

addProjection :: Name -> Field -> Name -> Tel.ClosedIdTel Type -> TC v ()
addProjection f n r tel = addDefinition f (Projection f n r tel)

addClause :: Name -> [Pattern] -> ClauseBody Term -> TC v ()
addClause f ps v = do
  def' <- getDefinition f
  let ext (Constant x Postulate a) = Function x a [c]
      ext (Function x a cs)        = Function x a (cs ++ [c])
      ext (Constant _ k _)         = error $ "Monad.addClause " ++ show k
      ext Constructor{}            = error $ "Monad.addClause constructor"
      ext Projection{}             = error $ "Monad.addClause projection"
  addDefinition f (ext def')
  where
    c = Clause ps v
