{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Check where

import           Prelude                          hiding (abs)

import           Data.Functor                     ((<$>))
import           Data.Void                        (Void, vacuous)

import           Syntax.Abstract                  (Name)
import qualified Syntax.Abstract                  as A
import qualified Impl                             as I
import qualified Impl.Telescope                   as I.Tel
import           Term
import           Term.View
import           Definition

whnfView :: I.Term v -> I.TC v (I.TermView v)
whnfView = undefined

-- type WithParsHandler = forall v.
--     I.Type v ->
--     -- The leftover from the 'I.Type' arg after the 'Names' have been
--     -- abstracted
--     [I.Term v] ->
--     -- The vars corresponding to the abstracted names.
--     I.TC v (I.Type v)

-- withPars :: I.ClosedType -> [Name] -> WithParsHandler
--          -> I.TC Void (I.ClosedTelescope I.Type)
-- withPars = go []
--   where
--     go :: [v] -> I.Type v -> [Name] -> WithParsHandler
--        -> I.TC v (I.Telescope I.Type Name)
--     go vars type_ []       ret = I.telescopeEmpty <$> ret type_ (map return vars)
--     go vars type_ (n : ns) ret =
--         I.telescopeExtend undefined n <$> go 

-- checkData
--     :: Name
--     -- ^ Name of the tycon
--     -> [Name]
--     -- ^ Name of the parameters to the tycons
--     -> [A.TypeSig]
--     -- ^ Data constructors
--     -> TC Void ()
-- checkData tyCon tyConPars absDataCons = do
--     tyConType <- getDefinition tyCon
--     addConstant tyCon Data tyConType
--     withPars tyConType tyConPars $ \tyConPars' tyConTypeEnd -> do
--         set <- I.unview Set
--         equalType tyConTypeEnd set
--         dataConTypeEnd <- unview $ App (Def tyCon) (map apply tyConPars')
--         mapM_ (checkDataCon tyCon dataConTypeEnd) absDataCons

-- checkDataCon
--     :: Name
--     -- ^ Name of the type constructor
--     -> Type v
--     -- ^ The type that should be found as return type of each data
--     -- constructor.
--     -> A.TypeSig
--     -- ^ The type of the data constructor
-- checkDataCon tyCon dataConTypeEnd (A.Sig dataCon absDataConType) =
--     atSrcLoc dataCon $ do
--         dataConType <- isType absDataConType
--         dataConTypeEnd <- discharge


-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: A.Expr -> I.Type v -> I.TC v (I.Term v)
check = undefined

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

checkData
    :: Name
    -- ^ Name of the tycon.
    -> [Name]
    -- ^ Names of parameters to the tycon.
    -> [A.TypeSig]
    -- ^ Types for the data constructors.
    -> I.TC Void ()
checkData = undefined

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
checkRec = undefined

-- Clause
---------

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
    :: forall v a.
       A.Pattern
    -> I.Type v
    -- ^ Type of the matched thing.
    -> (forall v'. (v -> v') -> Pattern -> I.Term v' -> I.TC v' a)
    -- ^ Handler taking the internal 'Pattern' and a 'I.Term'
    -- containing the term produced by it.
    -> I.TC v a
checkPattern synPat type_ ret = case synPat of
    A.VarP name ->
      I.extendContext name type_ $ \weaken v ->
      ret weaken VarP (I.unview (var v))
    A.WildP _ ->
      I.extendContext (A.name "_") type_ $ \weaken v ->
      ret weaken VarP (I.unview (var v))
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
                        I.Tel.instantiate (vacuous dataConType) typeConPars
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

-- Monad utils
--------------

addConstant :: Name -> ConstantKind -> I.ClosedType -> I.TC v ()
addConstant x k a = I.addDefinition x (Constant x k a)

addConstructor :: Name -> Name -> I.Tel.ClosedTelescope I.Type -> I.TC v ()
addConstructor c d tel = I.addDefinition c (Constructor c d tel)

addProjection :: Name -> Field -> Name -> I.Tel.ClosedTelescope I.Type -> I.TC v ()
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
