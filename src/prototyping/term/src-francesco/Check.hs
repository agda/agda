{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Check where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>))
import           Data.Void                        (Void, vacuous)

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

check :: A.Expr -> Type t v -> TC t v (t v)
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

infer :: A.Expr -> TC t v (t v, Type t v)
infer = undefined

-- Equality
-----------

checkEqual :: Type t v -> t v -> t v -> TC t v ()
checkEqual = undefined

inferEqual :: t v -> t v -> TC t v ()
inferEqual = undefined

-- Checking definitions
------------------------------------------------------------------------

checkDecl :: Term t => A.Decl -> ClosedTC t ()
checkDecl = undefined

checkTypeSig :: Term t => A.TypeSig -> ClosedTC t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType absType
    addConstant name Postulate type_

-- Data
-------

checkData
    :: Term t
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> ClosedTC t ()
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
    :: Term t
    => Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx t v
    -- ^ Ctx with the parameters of the tycon.
    -> Type t v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC t v ()
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
    :: Term t
    => Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Name of the parameters to the tycon.
    -> Name
    -- ^ Name of the data constructor.
    -> [A.TypeSig]
    -- ^ Fields of the record.
    -> ClosedTC t ()
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
    :: forall t v.
       Term t
    => [A.TypeSig]
    -> TC t v (Tel.ProxyTel t v)
checkFields = go Ctx.Empty
  where
    go :: Ctx.Ctx v t v' -> [A.TypeSig] -> TC t v' (Tel.ProxyTel t v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        extendContext field fieldType $ \_ _ ->
            go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: forall t v.
       Term t
    => Name
    -- ^ Type constructor.
    -> Ctx.ClosedCtx t v
    -- ^ A context with the parameters to the type constructor.
    -> TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.ProxyTel t (TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> TC t (TermVar v) ()
addProjections tyCon tyConPars self fields0 = go (zip [1..] fields0)
  where
    -- endType :: Type t v
    -- endType = pi (ctxApp (def tyCon) tyConPars) (toAbs (var self))

    go fields fieldTypes = case (fields, fieldTypes) of
        ([], Tel.Empty Tel.Proxy2) -> return ()
        ((ix, field) : fields', Tel.Cons fieldType fieldTypes') -> do
            undefined

-- -- Clause
-- ---------

-- -- TODO what about pattern coverage?

-- checkClause :: Name -> [A.Pattern] -> A.Expr -> I.TC Void ()
-- checkClause fun synPats synClauseBody = do
--     funType <- definitionType <$> I.getDefinition fun
--     checkPatterns synPats funType $ \_ pats _ clauseType -> do
--         clauseBody <- check synClauseBody clauseType
--         addClause fun pats =<< I.closeClauseBody clauseBody

-- checkPatterns
--     :: [A.Pattern]
--     -> I.Type v
--     -- ^ Type of the clause that has the given 'A.Pattern's in front.
--     -> (forall v'. (v -> v') -> [Pattern] -> [I.Term v'] -> I.Type v' -> I.TC v' a)
--     -- ^ Handler taking a function to weaken an external variable,
--     -- list of internal patterns, a list of terms produced by them, and
--     -- the type of the clause body (scoped over the pattern variables).
--     -> I.TC v a
-- checkPatterns [] type_ ret =
--     ret id [] [] type_
-- checkPatterns (synPat : synPats) type0 ret = I.atSrcLoc synPat $ do
--     type_ <- whnfView type0
--     case type_ of
--       Pi domain codomain ->
--         checkPattern synPat domain $ \weaken pat patVar -> do
--           let codomain'  = fmap weaken codomain
--           let codomain'' = I.absApply codomain' patVar
--           checkPatterns synPats codomain'' $ \weaken' pats patsVars -> do
--             let patVar' = fmap weaken' patVar
--             ret (weaken' . weaken) (pat : pats) (patVar' : patsVars)
--       _ ->
--         I.typeError $ "Expected function type: " ++ error "TODO show type_"

-- checkPattern
--     :: A.Pattern
--     -> I.Type v
--     -- ^ Type of the matched thing.
--     -> (forall v'. (v -> v') -> Pattern -> I.Term v' -> I.TC v' a)
--     -- ^ Handler taking a weakening function, the internal 'Pattern',
--     -- and a 'I.Term' containing the term produced by it.
--     -> I.TC v a
-- checkPattern synPat type_ ret = case synPat of
--     A.VarP name ->
--       I.extendContext name type_ $ \ctxV v ->
--       ret (I.Ctx.weaken ctxV) VarP (I.unview (var v))
--     A.WildP _ ->
--       I.extendContext (A.name "_") type_ $ \ctxV v ->
--       ret (I.Ctx.weaken ctxV) VarP (I.unview (var v))
--     A.ConP dataCon synPats -> do
--       dataConDef <- I.getDefinition dataCon
--       case dataConDef of
--         Constructor _ typeCon dataConType -> do
--           typeConDef <- I.getDefinition typeCon
--           case typeConDef of
--             Constant _ Data   _ -> return ()
--             Constant _ Record _ -> I.typeError $ "Pattern matching is not supported " ++
--                                                 "for the record constructor " ++ show dataCon
--             _                   -> I.typeError $ "checkPattern: impossible" ++ error "TODO show def"
--           synType <- whnfView type_
--           case synType of
--             App (Def typeCon') typeConPars0
--               | typeCon == typeCon', Just typeConPars <- mapM isApply typeConPars0 -> do
--                 let dataConTypeNoPars =
--                         I.Tel.unId2 $ I.Tel.instantiate (vacuous dataConType) typeConPars
--                 checkPatterns synPats dataConTypeNoPars $ \weaken pats patsVars _ -> do
--                   let t = I.unview (App (Con dataCon) $ map Apply patsVars)
--                   ret weaken (ConP dataCon pats) t
--             _ ->
--               I.typeError $ show dataCon ++
--                             " does not construct an element of " ++ error "TODO show type_"
--         _ ->
--           I.typeError $ "Should be constructor: " ++ show dataCon

-- Utils
------------------------------------------------------------------------

equalType :: Term t => Type t v -> Type t v -> TC t v ()
equalType a b = checkEqual set a b

isApply :: Elim t v -> Maybe (t v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isType :: Term t => A.Expr -> TC t v (Type t v)
isType abs = check abs set

definitionType :: Definition t -> ClosedType t
definitionType = undefined

absName :: t (TermVar v) -> Name
absName = undefined

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
    :: Term t
    => Type t v
    -- ^ Type to unroll
    -> [Name]
    -- ^ Names to give to each parameter
    -> (forall v'. Ctx.Ctx v t v' -> Type t v' -> TC t v' a)
    -- ^ Handler taking a context with accumulated domains of the pis
    -- and the final codomain.
    -> TC t v a
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
    :: Term t
    => Type t v
    -- ^ Type to unroll
    -> (forall v'. Ctx.Ctx v t v' -> Type t v' -> TC t v' a)
    -- ^ Handler taking a weakening function, the list of domains
    -- of the unrolled pis, the final codomain.
    -> TC t v a
unrollPi type_ ret = do
    synType :: TermView (TermAbs t) t v <- whnfView type_
    case synType of
        Pi domain (codomain :: TermAbs t v) -> do
            let codomain' = fromAbs codomain
            extendContext (absName codomain') domain $ \_v ctxV ->
                unrollPi codomain' $ \ctxVs endType ->
                ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            ret Ctx.Empty type_

-- Monad utils
--------------

addConstant :: Name -> ConstantKind -> ClosedType t -> TC t v ()
addConstant x k a = addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> Tel.ClosedIdTel t -> TC t v ()
addConstructor c d tel = addDefinition c (Constructor c d tel)

addProjection :: Name -> Field -> Name -> Tel.ClosedIdTel t -> TC t v ()
addProjection f n r tel = addDefinition f (Projection f n r tel)

addClause :: Name -> [Pattern] -> ClauseBody t -> TC t v ()
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
