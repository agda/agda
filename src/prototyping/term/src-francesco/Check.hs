{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Check where

import           Prelude                          hiding (abs)

import           Data.Functor                     ((<$>))
import           Data.Void                        (Void, vacuous)

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Syntax.Abstract                  as A
import qualified Impl                             as I
import qualified Impl.Context                     as I.Ctx
import qualified Impl.Telescope                   as I.Tel
import           Term
import           Term.View
import           Definition

whnfView :: I.Term v -> I.TC v (I.TermView v)
whnfView = undefined

-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: A.Expr -> I.Type v -> I.TC v (I.Term v)
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

infer :: A.Expr -> I.TC v (I.Term v, I.Type v)
infer = undefined

-- Equality
-----------

checkEqual :: I.Type v -> I.Term v -> I.Term v -> I.TC v ()
checkEqual = undefined

inferEqual :: I.Term v -> I.Term v -> I.TC v ()
inferEqual = undefined

-- Checking definitions
------------------------------------------------------------------------

checkDecl :: A.Decl -> I.TC Void ()
checkDecl = undefined

checkTypeSig :: A.TypeSig -> I.TC Void ()
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
    -> I.TC Void ()
checkData tyCon tyConPars dataCons = do
    tyConType <- definitionType <$> I.getDefinition tyCon
    addConstant tyCon Data tyConType
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        equalType endType (I.unview Set)
        -- TODO maybe we should expose a 'vars' function from the Ctx
        -- and do the application ourselves.
        let appliedTyConType = I.Ctx.app (I.unview (App (Def tyCon) [])) tyConPars'
        mapM_ (checkConstr tyCon tyConPars' appliedTyConType) dataCons

checkConstr
    :: Name
    -- ^ Name of the tycon.
    -> I.Ctx.ClosedCtx I.Type v
    -- ^ Ctx with the parameters of the tycon.
    -> I.Type v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> I.TC v ()
checkConstr tyCon tyConPars appliedTyConType (A.Sig dataCon synDataConType) =
    I.atSrcLoc dataCon $ do
        dataConType <- isType synDataConType
        unrollPi dataConType $ \vs endType -> do
            let appliedTyConType' = fmap (I.Ctx.weaken vs) appliedTyConType
            equalType appliedTyConType' endType
        addConstructor dataCon tyCon (I.Tel.idTel tyConPars dataConType)

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
    -> I.TC Void ()
checkRec tyCon tyConPars dataCon fields = do
    tyConType <- definitionType <$> I.getDefinition tyCon
    addConstant tyCon Record tyConType
    unrollPiWithNames tyConType tyConPars $ \tyConPars' endType -> do
        equalType endType (I.unview Set)
        fieldsTel <- checkFields fields
        let appliedTyConType =
                I.Ctx.app (I.unview (App (Def tyCon) [])) tyConPars'
        I.extendContext (A.name "_") appliedTyConType $ \selfCtx self -> do
            addProjections
                tyCon tyConPars' self (map A.typeSigName fields) $
                (fmap (I.Ctx.weaken selfCtx) fieldsTel)
        addConstructor dataCon tyCon (I.Tel.idTel tyConPars' appliedTyConType)

checkFields
    :: forall v.
       [A.TypeSig]
    -> I.TC v (I.Tel.ProxyTel I.Type v)
checkFields = go I.Ctx.empty
  where
    go :: I.Ctx.Ctx v I.Type v' -> [A.TypeSig]
       -> I.TC v' (I.Tel.ProxyTel I.Type v)
    go ctx [] =
        return $ I.Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        I.extendContext field fieldType $ \_ _ ->
            go (I.Ctx.extend ctx field fieldType) fields

addProjections
    :: Name
    -- ^ Type constructor.
    -> I.Ctx.ClosedCtx I.Type v
    -- ^ A context with the parameters to the type constructor.
    -> I.TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> I.Tel.ProxyTel I.Type (I.TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> I.TC (I.TermVar v) ()
addProjections = undefined

-- Clause
---------

-- TODO what about pattern coverage?

checkClause :: Name -> [A.Pattern] -> A.Expr -> I.TC Void ()
checkClause fun synPats synClauseBody = do
    funType <- definitionType <$> I.getDefinition fun
    checkPatterns synPats funType $ \_ pats _ clauseType -> do
        clauseBody <- check synClauseBody clauseType
        addClause fun pats =<< I.closeClauseBody clauseBody

checkPatterns
    :: [A.Pattern]
    -> I.Type v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (forall v'. (v -> v') -> [Pattern] -> [I.Term v'] -> I.Type v' -> I.TC v' a)
    -- ^ Handler taking a function to weaken an external variable,
    -- list of internal patterns, a list of terms produced by them, and
    -- the type of the clause body (scoped over the pattern variables).
    -> I.TC v a
checkPatterns [] type_ ret =
    ret id [] [] type_
checkPatterns (synPat : synPats) type0 ret = I.atSrcLoc synPat $ do
    type_ <- whnfView type0
    case type_ of
      Pi domain codomain ->
        checkPattern synPat domain $ \weaken pat patVar -> do
          let codomain'  = fmap weaken codomain
          let codomain'' = I.absApply codomain' patVar
          checkPatterns synPats codomain'' $ \weaken' pats patsVars -> do
            let patVar' = fmap weaken' patVar
            ret (weaken' . weaken) (pat : pats) (patVar' : patsVars)
      _ ->
        I.typeError $ "Expected function type: " ++ error "TODO show type_"

checkPattern
    :: A.Pattern
    -> I.Type v
    -- ^ Type of the matched thing.
    -> (forall v'. (v -> v') -> Pattern -> I.Term v' -> I.TC v' a)
    -- ^ Handler taking a weakening function, the internal 'Pattern',
    -- and a 'I.Term' containing the term produced by it.
    -> I.TC v a
checkPattern synPat type_ ret = case synPat of
    A.VarP name ->
      I.extendContext name type_ $ \ctxV v ->
      ret (I.Ctx.weaken ctxV) VarP (I.unview (var v))
    A.WildP _ ->
      I.extendContext (A.name "_") type_ $ \ctxV v ->
      ret (I.Ctx.weaken ctxV) VarP (I.unview (var v))
    A.ConP dataCon synPats -> do
      dataConDef <- I.getDefinition dataCon
      case dataConDef of
        Constructor _ typeCon dataConType -> do
          typeConDef <- I.getDefinition typeCon
          case typeConDef of
            Constant _ Data   _ -> return ()
            Constant _ Record _ -> I.typeError $ "Pattern matching is not supported " ++
                                                "for the record constructor " ++ show dataCon
            _                   -> I.typeError $ "checkPattern: impossible" ++ error "TODO show def"
          synType <- whnfView type_
          case synType of
            App (Def typeCon') typeConPars0
              | typeCon == typeCon', Just typeConPars <- mapM isApply typeConPars0 -> do
                let dataConTypeNoPars =
                        I.Tel.unId2 $ I.Tel.instantiate (vacuous dataConType) typeConPars
                checkPatterns synPats dataConTypeNoPars $ \weaken pats patsVars _ -> do
                  let t = I.unview (App (Con dataCon) $ map Apply patsVars)
                  ret weaken (ConP dataCon pats) t
            _ ->
              I.typeError $ show dataCon ++
                            " does not construct an element of " ++ error "TODO show type_"
        _ ->
          I.typeError $ "Should be constructor: " ++ show dataCon

-- Utils
------------------------------------------------------------------------

equalType :: I.Type v -> I.Type v -> I.TC v ()
equalType a b = do
  let set = I.unview Set
  checkEqual set a b

isApply :: I.TermElim v -> Maybe (I.Term v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

isType :: A.Expr -> I.TC v (I.Type v)
isType abs = do
    let set = I.unview Set
    check abs set

definitionType :: I.TermDefinition -> I.ClosedType
definitionType = undefined

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
    :: I.Type v
    -- ^ Type to unroll
    -> [Name]
    -- ^ Names to give to each parameter
    -> (forall v'. I.Ctx.Ctx v I.Type v' -> I.Type v' -> I.TC v' a)
    -- ^ Handler taking a context with accumulated domains of the pis
    -- and the final codomain.
    -> I.TC v a
unrollPiWithNames type_ []             ret = ret I.Ctx.empty type_
unrollPiWithNames type_ (name : names) ret = do
    synType <- whnfView type_
    case synType of
        Pi domain codomain ->
            I.extendContext name domain $ \ctxV _v ->
            unrollPiWithNames (I.absBody codomain) names $ \ctxVs endType ->
            ret (ctxV I.Ctx.++ ctxVs) endType
        _ ->
            I.typeError $ "Expected function type: " ++ error "TODO show synType"

unrollPi
    :: I.Type v
    -- ^ Type to unroll
    -> (forall v'. I.Ctx.Ctx v I.Type v' -> I.Type v' -> I.TC v' a)
    -- ^ Handler taking a weakening function, the list of domains
    -- of the unrolled pis, the final codomain.
    -> I.TC v a
unrollPi type_ ret = do
    synType <- whnfView type_
    case synType of
        Pi domain codomain ->
            I.extendContext (I.absName codomain) domain $ \ctxV _v ->
            unrollPi (I.absBody codomain) $ \ctxVs endType ->
            ret (ctxV I.Ctx.++ ctxVs) endType
        _ ->
            ret I.Ctx.empty type_

-- Monad utils
--------------

addConstant :: Name -> ConstantKind -> I.ClosedType -> I.TC v ()
addConstant x k a = I.addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> I.Tel.ClosedIdTel I.Type -> I.TC v ()
addConstructor c d tel = I.addDefinition c (Constructor c d tel)

addProjection :: Name -> Field -> Name -> I.Tel.ClosedIdTel I.Type -> I.TC v ()
addProjection f n r tel = I.addDefinition f (Projection f n r tel)

addClause :: Name -> [Pattern] -> I.ClauseBody -> I.TC v ()
addClause f ps v = do
  def <- I.getDefinition f
  let ext (Constant x Postulate a) = Function x a [c]
      ext (Function x a cs)        = Function x a (cs ++ [c])
      ext (Constant _ k _)         = error $ "Monad.addClause " ++ show k
      ext Constructor{}            = error $ "Monad.addClause constructor"
      ext Projection{}             = error $ "Monad.addClause projection"
  I.addDefinition f (ext def)
  where
    c = Clause ps v
