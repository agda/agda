module Check (checkProgram) where

import           Prelude                          hiding (abs, pi)

import           Data.Functor                     ((<$>))
import           Data.Foldable                    (foldMap)
import           Data.Monoid                      (Monoid(..),(<>))
import           Debug.Trace                      (trace)
import qualified Data.HashSet                     as HS
import           Control.Monad                    (when, guard, unless)
import           Data.List                        (nub)
import           Data.Traversable                 (traverse)
import           Prelude.Extras                   ((==#))
import           Data.Proxy                       (Proxy)
import           Bound                            hiding (instantiate, abstract)
import           Data.Maybe                       (maybeToList)

import           Data.Void                        (vacuous)
import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import qualified Syntax.Abstract                  as A
import           Types.Definition
import qualified Types.Context                    as Ctx
import qualified Types.Telescope                  as Tel
import           Types.Monad
import           Types.Term
import           Types.Var
import           Text.PrettyPrint.Extended        (render)

-- Main functions
------------------------------------------------------------------------

-- Type checking
----------------

check :: (IsVar v, IsTerm t) => A.Expr -> Type t v -> TC t v (Term t v)
check synT type_ = atSrcLoc synT $ case synT of
  A.Con dataCon synArgs -> do
    (tyCon, dataConType) <- getConstructorDefinition dataCon
    typeView <- whnfView type_
    case typeView of
      App (Def tyCon') tyConArgs0
        | tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 -> do
          let appliedDataConType = Tel.substs (vacuous dataConType) tyConArgs
          args <- checkConArgs synArgs appliedDataConType
          return (con dataCon args)
      _ -> checkError $ ConstructorTypeError synT $ unview typeView
  A.Refl _ -> do
    typeView <- whnfView type_
    case typeView of
      Equal type' x y -> do
        checkEqual type' x y
        return refl
      _ ->
          checkError $ NotEqualityType (unview typeView)
  A.Meta _ ->
    addFreshMetaVar type_
  A.Lam name synBody -> do
    typeView <- whnfView type_
    case typeView of
      Pi domain codomain -> do
         body <- extendContext name domain $ \_ _ ->
           check synBody (fromAbs codomain)
         return $ lam (toAbs body)
      App (Meta _) _ -> do
        dom <- addFreshMetaVar set
        cod <- extendContext name dom $ \ _ _ -> addFreshMetaVar set
        checkEqual set (unview typeView) (pi dom (toAbs cod))
        body <- extendContext name dom $ \ _ _ -> check synBody cod
        return $ lam (toAbs body)
      _ ->
        checkError $ LambdaTypeError synT (unview typeView)
  _ -> do
    (t, type') <- infer synT
    equalType type_ type'
    return t

checkConArgs :: (IsVar v, IsTerm t) => [A.Expr] -> Type t v -> TC t v [t v]
checkConArgs []                 _     = return []
checkConArgs (synArg : synArgs) type_ = atSrcLoc synArg $ do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      arg <- check synArg domain
      (arg :) <$> checkConArgs synArgs (instantiate codomain arg)
    _ ->
      checkError $ ExpectedFunctionType (unview typeView) (Just synArg)

infer :: (IsVar v, IsTerm t) => A.Expr -> TC t v (Term t v, Type t v)
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
  _ -> do
    type_ <- addFreshMetaVar set
    t <- check synT type_
    return (t, type_)

checkSpine :: (IsVar v, IsTerm t)
           => Term t v -> [A.Elim] -> Type t v -> TC t v (Term t v, Type t v)
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
        checkError $ ExpectedFunctionType (unview typeView) (Just synArg)

inferHead :: (IsVar v, IsTerm t) => A.Head -> TC t v (Head v, Type t v)
inferHead synH = atSrcLoc synH $ case synH of
  A.Var name -> do
    (v, type_) <- getTypeOfName name
    return (Var v, type_)
  A.Def name -> do
    type_ <- definitionType <$> getDefinition name
    return (Def name, vacuous type_)
  A.J{} ->
    error "TODO inferHead J"

-- Equality
-----------

checkEqual :: (IsVar v, IsTerm t) => Type t v -> Term t v -> Term t v -> TC t v ()
checkEqual _ x y | x ==# y =
  return ()
checkEqual type_ x y = do
  typeView <- whnfView type_
  xView <- whnfView x
  yView <- whnfView y
  case (typeView, xView, yView) of
    (Pi domain codomain, _, _) -> do
      let codomain' = fromAbs codomain
      extendContext (getName codomain') domain $ \v ctxV -> do
        let v' = var v
        let x' = eliminate (fmap (Ctx.weaken ctxV) x) [Apply v']
        let y' = eliminate (fmap (Ctx.weaken ctxV) y) [Apply v']
        checkEqual codomain' x' y'
    (App (Def tyCon) tyConPars0, Con dataCon dataConArgs1, Con dataCon' dataConArgs2)
      | Just tyConPars <- mapM isApply tyConPars0
      , dataCon == dataCon' -> do
        (tyCon', dataConType) <- getConstructorDefinition dataCon
        unless (tyCon == tyCon') $ error $
            "impossible.checkEqual: mismatching type constructors " ++
            show tyCon ++ ", " ++ show tyCon'
        let appliedDataConType = Tel.substs (vacuous dataConType) tyConPars
        equalConArgs appliedDataConType dataCon dataConArgs1 dataConArgs2
    (_, Pi dom1 cod1, Pi dom2 cod2) -> do
       checkEqual set dom1 dom2
       let cod1' = fromAbs cod1
       extendContext (getName cod1') dom1 $ \ _ _ -> checkEqual set cod1' (fromAbs cod2)
    (_, Equal type1 x1 y1, Equal type2 x2 y2) -> do
       checkEqual set type1 type2
       checkEqual type1 x1 x2
       checkEqual type1 y1 y2
    (_, Refl, Refl) -> do
      return ()
    (_, App (Meta mv) elims, t) ->
      metaAssign mv elims (unview t)
    (_, t, App (Meta mv) elims) ->
      metaAssign mv elims (unview t)
    (_, App h1 elims1, App h2 elims2) | h1 == h2 -> do
      h1Type <- case h1 of
        Var v   -> getTypeOfVar v
        Def f   -> vacuous . definitionType <$> getDefinition f
        J       -> error "TODO typeOfJ"
        Meta _  -> error "impossible.checkEqual: can't decompose with metavariable heads"
      equalSpine h1Type (unview (App h1 [])) elims1 elims2
    _ ->
      checkError $ TermsNotEqual (unview xView) (unview yView)

equalSpine
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type of the head.
    -> Term t v
    -- ^ Head.
    -> [Elim (Term t) v] -> [Elim (Term t) v] -> TC t v ()
equalSpine _ _ [] [] =
  return ()
equalSpine type_ h (Apply arg1 : elims1) (Apply arg2 : elims2) = do
  typeView <- whnfView type_
  case typeView of
    Pi domain codomain -> do
      checkEqual domain arg1 arg2
      equalSpine (instantiate codomain arg1) (eliminate h [Apply arg1]) elims1 elims2
    _ ->
      error $ "impossible.equalSpine: Expected function type " ++ render typeView
equalSpine type_ h (Proj proj projIx : elims1) (Proj proj' projIx' : elims2)
  | proj == proj' && projIx == projIx' = do
    (h', type') <- applyProjection proj h type_
    equalSpine type' h' elims1 elims2
equalSpine type_ _ elims1 elims2 =
  checkError $ SpineNotEqual type_ elims1 elims2

-- | INVARIANT: the two lists are the of the same length.
equalConArgs
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type of the head.
    -> Name -> [Term t v] -> [Term t v] -> TC t v ()
equalConArgs type_ dataCon xs ys = do
  expandedCon <- unrollPi type_ $ \ctx _ -> return $
                 ctxLam ctx (con dataCon (map var (ctxVars ctx)))
  equalSpine type_ expandedCon (map Apply xs) (map Apply ys)

applyProjection
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the projection
    -> Term t v
    -- ^ Head
    -> Type t v
    -- ^ Type of the head
    -> TC t v (Term t v, Type t v)
applyProjection proj h type_ = do
  projDef <- getDefinition proj
  case projDef of
    Projection _ projIx tyCon projType -> do
      let h' = eliminate h [Proj proj projIx]
      typeView <- whnfView type_
      tyConArgs <- case typeView of
        App (Def tyCon') tyConArgs0
          | tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 -> do
            return tyConArgs
        App (Meta mv) mvArgs -> do
          -- If we have a meta, we instantiate making it the righ type,
          -- and putting fresh metas as parameters.
          liftClosed $ do
            mvType <- getTypeOfMetaVar mv
            mvT <- unrollPi mvType $ \ctxMvArgs _ -> do
              Constant _ Postulate tyConType <- getDefinition tyCon
              tyConParsTel <- unrollPi (vacuous tyConType) $ \ctx ->
                              return . Tel.idTel ctx
              tyConParsMvs <- createTyConParsMvs tyConParsTel
              return $
                ctxLam ctxMvArgs $ eliminate (def tyCon) (map Apply tyConParsMvs)
            instantiateMetaVar mv mvT
          -- Once instantiated, we re-evaluate the type and extract the
          -- arguments of the type constructor.
          typeView' <- whnfView $ unview $ App (Meta mv) mvArgs
          case typeView' of
            App (Def tyCon') tyConArgs0
              | tyCon == tyCon', Just tyConArgs <- mapM isApply tyConArgs0 ->
                return tyConArgs
            _ ->
              error "impossible.applyProjection: Meta doesn't reduce"
        _ ->
          checkError $ ExpectingRecordType (unview typeView)
      let appliedProjType = view $ Tel.substs (vacuous projType) tyConArgs
      case appliedProjType of
        Pi _ endType ->
          return (h', instantiate endType h)
        _ ->
          error $ "impossible.applyProjection: " ++ render appliedProjType
    _ ->
      error $ "impossible.applyProjection: " ++ render projDef
  where
    createTyConParsMvs :: (IsTerm t) => Tel.IdTel (Type t) v -> TC t v [Term t v]
    createTyConParsMvs (Tel.Empty _) =
      return []
    createTyConParsMvs (Tel.Cons (name, type') tel) = do
      mv  <- addFreshMetaVar type'
      mvs <- extendContext name type' $ \_ _ -> createTyConParsMvs tel
      return (mv : map (\t -> instantiate (toAbs t) mv) mvs)

-- MetaVar handling
-------------------

metaAssign
    :: (IsVar v, IsTerm t)
    => MetaVar -> [Elim (Term t) v] -> Term t v -> TC t v ()
metaAssign mv elims t =
    case distinctVariables elims of
        Nothing ->
            error "TODO metaAssign stuck"
        Just vs -> do
            t' <- closeTerm $ lambdaAbstract vs t
            let mvs = metaVars t'
            when (mv `HS.member` mvs) $ do
                error $
                    "impossible.metaAssign: Attempt at recursive instantiation: " ++
                    render mv ++ " := " ++ renderView t'
            instantiateMetaVar mv t'

-- | Collects all the rigidly occurring variables in a term.
--
-- With "rigidly occurring" here we mean either occurring as arguments
-- of constructors or occurring as arguments of object variables that
-- might be substituted with a metavariable.
--
-- Note that we don't specify how precise the detection of said
-- "substitutable" object variables is we might be more conservative
-- than possible.
rigidVars
    :: forall t v0.
       (IsVar v0, IsTerm t)
    => [v0]
    -- ^ vars that count as flexible, and so also flexible contexts
    -> Term t v0 -> TC t v0 [v0]
rigidVars vs t0 = do
  sig <- getSignature
  let
    go :: (IsVar v)
       => (v -> Maybe v0)
       -> (v -> Bool)
       -- ^ vars that count as flexible, and so also flexible contexts
       -> Term t v -> [v0]
    go strengthen flex t =
      case view (whnf sig t) of
        Lam body ->
          go (lift strengthen) (addNew flex) (fromAbs body)
        Pi domain codomain ->
          go strengthen flex domain <>
          go (lift strengthen) (ignoreNew flex) (fromAbs codomain)
        Equal type_ x y ->
          foldMap (go strengthen flex) [type_, x, y]
        App (Var v) elims ->
          if flex v
          then mempty
          else maybeToList (strengthen v) <>
               foldMap (go strengthen flex) [t' | Apply t' <- elims]
        App (Def _) elims ->
          foldMap (go strengthen flex) [t' | Apply t' <- elims]
        App J elims ->
          foldMap (go strengthen flex) [t' | Apply t' <- elims]
        App (Meta _) _ ->
          mempty
        Set ->
          mempty
        Refl ->
          mempty
        Con _ args ->
          foldMap (go strengthen flex) args

    lift :: (v -> Maybe v0) -> TermVar v -> Maybe v0
    lift _ (B _) = Nothing
    lift f (F v) = f v

    ignoreNew _ (B _) = False
    ignoreNew f (F v) = f v

    addNew _ (B _) = True
    addNew f (F v) = f v

  return $ go Just (`elem` vs) t0

distinctVariables :: (IsVar v, IsTerm t) => [Elim (Term t) v] -> Maybe [v]
distinctVariables elims = do
    vs <- mapM isVar elims
    guard (vs == nub vs)
    return vs
  where
    isVar (Apply t) = case view t of
        App (Var v) [] -> Just v
        _              -> Nothing
    isVar _ =
        Nothing

-- | Creates a term in the same context as the original term but lambda
-- abstracted over the given variables.
lambdaAbstract :: (IsVar v, IsTerm t) => [v] -> Term t v -> Term t v
lambdaAbstract []       t = t
lambdaAbstract (v : vs) t = unview $ Lam $ abstract v $ lambdaAbstract vs t

closeTerm :: (IsVar v, IsTerm t) => Term t v -> TC t v (Closed (Term t))
closeTerm = traverse close
  where
    close = checkError . FreeVariableInEquatedTerm

createPrunedMeta
    :: (IsVar v, IsTerm t)
    => [v]
    -- ^ The list of allowed variables.
    -> MetaVar
    -- ^ The original metavariable, whose arguments we want to prune.
    -> [Term t v]
    -- ^ The arguments that we want to prune.
    -> TC t v (Term t v)
    -- ^ The term containing the new metavariable applied to the pruned
    -- arguments
createPrunedMeta _vs0 mv _mvArgs = do
    mvType <- getTypeOfMetaVar mv
    vacuous <$> liftClosed (createNewMeta mvType kills0 [])
  where
    -- This list specifies the arguments which should be killed.  Note
    -- that if an argument is to be killed it is also guaranteed not to
    -- appear in the type of any following arguments.
    kills0 :: [Bool]
    kills0 = error "TODO createPrunedMeta kills"

    createNewMeta :: (IsTerm t) => Type t v -> [Bool] -> [v] -> TC t v (Term t v)
    createNewMeta type_ [] vs = do
      mv' <- addFreshMetaVar type_
      return (eliminate mv' (map (Apply . var) (reverse vs)))
    createNewMeta type_ (kill : kills) vs = do
      typeView <- whnfView type_
      case typeView of
        Pi domain codomain | not kill -> do
          let codomain' = fromAbs codomain
          t <- extendContext (getName codomain') domain $ \v _ ->
               createNewMeta codomain' kills (v : map F vs)
          return (lam (toAbs t))
        Pi _domain codomain -> do
          let codomain' =
                instantiate codomain $
                error "impossible.createPrunedMeta: killed argument appears later in type."
          createNewMeta codomain' kills vs
        _ ->
          error "impossible.createPrunedMeta: metavar type too short."

-- Checking definitions
------------------------------------------------------------------------

checkProgram :: (IsTerm t) => Proxy t -> [A.Decl] -> ClosedTC t ()
checkProgram _ = mapM_ checkDecl

checkDecl :: (IsTerm t) => A.Decl -> ClosedTC t ()
checkDecl decl = atSrcLoc decl $ do
  trace (render decl) $ return ()
  case decl of
    A.TypeSig sig      -> checkTypeSig sig
    A.DataDef d xs cs  -> checkData d xs cs
    A.RecDef d xs c fs -> checkRec d xs c fs
    A.FunDef f ps b    -> checkClause f ps b

checkTypeSig :: (IsTerm t) => A.TypeSig -> ClosedTC t ()
checkTypeSig (A.Sig name absType) = do
    type_ <- isType absType
    addConstant name Postulate type_

-- Data
-------

checkData
    :: (IsTerm t)
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
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Name of the tycon.
    -> Ctx.ClosedCtx (Type t) v
    -- ^ Ctx with the parameters of the tycon.
    -> Type t v
    -- ^ Tycon applied to the parameters.
    -> A.TypeSig
    -- ^ Data constructor.
    -> TC t v ()
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
    :: (IsTerm t)
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
        Tel.unTel fieldsTel $ \fieldsCtx Tel.Proxy2 ->
            addConstructor dataCon tyCon $
            Tel.idTel tyConPars' $
            ctxPi fieldsCtx (fmap (Ctx.weaken fieldsCtx) appliedTyConType)

checkFields
    :: (IsVar v, IsTerm t) => [A.TypeSig] -> TC t v (Tel.ProxyTel (Type t) v)
checkFields = go Ctx.Empty
  where
    go :: (IsVar v, IsVar v', IsTerm t)
       => Ctx.Ctx v (Type t) v' -> [A.TypeSig] -> TC t v' (Tel.ProxyTel (Type t) v)
    go ctx [] =
        return $ Tel.proxyTel ctx
    go ctx (A.Sig field synFieldType : fields) = do
        fieldType <- isType synFieldType
        extendContext field fieldType $ \_ _ ->
            go (Ctx.Snoc ctx (field, fieldType)) fields

addProjections
    :: (IsVar v, IsTerm t)
    => Name
    -- ^ Type constructor.
    -> Ctx.ClosedCtx (Type t) v
    -- ^ A context with the parameters to the type constructor.
    -> TermVar v
    -- ^ Variable referring to the value of type record type itself,
    -- which is the last argument of each projection ("self").  We have
    -- a 'TermVar' here (and after) precisely because we're scoping over
    -- the self element after the tycon parameters above.
    -> [Name]
    -- ^ Names of the remaining fields.
    -> Tel.ProxyTel (Type t) (TermVar v)
    -- ^ Telescope holding the types of the next fields, scoped
    -- over the types of the previous fields.
    -> TC t (TermVar v) ()
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
        (_, _) -> error "impossible.addProjections: impossible: lengths do not match"

-- Clause
---------

-- TODO what about pattern coverage?

checkClause :: (IsTerm t) => Name -> [A.Pattern] -> A.Expr -> ClosedTC t ()
checkClause fun synPats synClauseBody = do
    funType <- definitionType <$> getDefinition fun
    checkPatterns synPats funType $ \_ pats _ clauseType -> do
        clauseBody <- check synClauseBody clauseType
        addClause fun pats =<< closeClauseBody clauseBody

checkPatterns
    :: (IsVar v, IsTerm t)
    => [A.Pattern]
    -> Type t v
    -- ^ Type of the clause that has the given 'A.Pattern's in front.
    -> (∀ v'. (IsVar v') => (v -> v') -> [Pattern] -> [Term t v'] -> Type t v' -> TC t v' a)
    -- ^ Handler taking a function to weaken an external variable,
    -- list of internal patterns, a list of terms produced by them, and
    -- the type of the clause body (scoped over the pattern variables).
    -> TC t v a
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
        checkError $ ExpectedFunctionType (unview typeView) Nothing

checkPattern
    :: (IsVar v, IsTerm t)
    => A.Pattern
    -> Type t v
    -- ^ Type of the matched thing.
    -> (∀ v'. (IsVar v') => (v -> v') -> Pattern -> Term t v' -> TC t v' a)
    -- ^ Handler taking a weakening function, the internal 'Pattern',
    -- and a 'Term' containing the term produced by it.
    -> TC t v a
checkPattern synPat type_ ret = case synPat of
    A.VarP name ->
      extendContext name type_ $ \v ctxV ->
      ret (Ctx.weaken ctxV) VarP (var v)
    A.WildP _ ->
      extendContext (A.name "_") type_ $ \v ctxV ->
      ret (Ctx.weaken ctxV) VarP (var v)
    A.ConP dataCon synPats -> do
      (typeCon, dataConType) <- getConstructorDefinition dataCon
      typeConDef <- getDefinition typeCon
      case typeConDef of
        Constant _ Data   _ -> return ()
        Constant _ Record _ -> checkError $ PatternMatchOnRecord synPat typeCon
        _                   -> error $ "impossible.checkPattern" ++ render typeConDef
      typeView <- whnfView type_
      case typeView of
        App (Def typeCon') typeConPars0
          | typeCon == typeCon', Just typeConPars <- mapM isApply typeConPars0 -> do
            let dataConTypeNoPars =
                    Tel.substs (vacuous dataConType) typeConPars
            checkPatterns synPats dataConTypeNoPars $ \weaken_ pats patsVars _ -> do
              let t = unview (Con dataCon patsVars)
              ret weaken_ (ConP dataCon pats) t
        _ ->
          checkError $ MismatchingPattern type_ synPat

-- Utils
------------------------------------------------------------------------

equalType :: (IsVar v, IsTerm t) => Type t v -> Type t v -> TC t v ()
equalType a b = checkEqual set a b

isType :: (IsVar v, IsTerm t) => A.Expr -> TC t v (Type t v)
isType abs = check abs set

isApply :: Elim (Term t) v -> Maybe (Term t v)
isApply (Apply v) = Just v
isApply Proj{}    = Nothing

definitionType :: (IsTerm t) => Definition t -> Closed (Type t)
definitionType (Constant _ _ type_)   = type_
definitionType (Constructor _ _ tel)  = telPi tel
definitionType (Projection _ _ _ tel) = telPi tel
definitionType (Function _ type_ _)   = type_

-- Unrolling Pis
----------------

-- TODO remove duplication

unrollPiWithNames
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type to unroll
    -> [Name]
    -- ^ Names to give to each parameter
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t v' a)
    -- ^ Handler taking a context with accumulated domains of the pis
    -- and the final codomain.
    -> TC t v a
unrollPiWithNames type_ []             ret = ret Ctx.Empty type_
unrollPiWithNames type_ (name : names) ret = do
    typeView <- whnfView type_
    case typeView of
        Pi domain codomain ->
            extendContext name domain $ \_v ctxV ->
            unrollPiWithNames (fromAbs codomain) names $ \ctxVs endType ->
            ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            checkError $ ExpectedFunctionType (unview typeView) Nothing

unrollPi
    :: (IsVar v, IsTerm t)
    => Type t v
    -- ^ Type to unroll
    -> (∀ v'. (IsVar v') => Ctx.Ctx v (Type t) v' -> Type t v' -> TC t v' a)
    -- ^ Handler taking a weakening function, the list of domains
    -- of the unrolled pis, the final codomain.
    -> TC t v a
unrollPi type_ ret = do
    typeView <- whnfView type_
    case typeView of
        Pi domain codomain -> do
            let codomain' = fromAbs codomain
            extendContext (getName codomain') domain $ \_v ctxV ->
                unrollPi codomain' $ \ctxVs endType ->
                ret (ctxV Ctx.++ ctxVs) endType
        _ ->
            ret Ctx.Empty type_

-- Definition utils
-------------------

addConstant
    :: (IsVar v, IsTerm t)
    => Name -> ConstantKind -> Closed (Type t) -> TC t v ()
addConstant x k a = addDefinition x (Constant x k a)

addConstructor
    :: (IsVar v, IsTerm t)
    => Name -> Name -> Tel.ClosedIdTel (Type t) -> TC t v ()
addConstructor c d tel = addDefinition c (Constructor c d tel)

addProjection
    :: (IsVar v, IsTerm t)
    => Name -> Field -> Name -> Tel.ClosedIdTel (Type t) -> TC t v ()
addProjection f n r tel = addDefinition f (Projection f n r tel)

addClause
    :: (IsVar v, IsTerm t)
    => Name -> [Pattern] -> ClauseBody (Term t) -> TC t v ()
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

getConstructorDefinition
    :: (IsVar v, IsTerm t)
    => Name -> TC t v (Name, Tel.ClosedIdTel t)
getConstructorDefinition dataCon = do
  def' <- getDefinition dataCon
  case def' of
    Constructor _ tyCon dataConType ->
      return (tyCon, dataConType)
    _ ->
      error $ "impossible.getConstructorDefinition: non data constructor " ++
              show dataCon

-- Telescope utils
------------------

telPi :: (IsVar v, IsTerm t) => Tel.IdTel (Type t) v -> Type t v
telPi tel = Tel.unTel tel $ \ctx endType -> ctxPi ctx (Tel.unId2 endType)

-- Whnf'ing and view'ing
------------------------

whnfView :: (IsTerm t) => t v -> TC t v' (TermView t v)
whnfView t = do
  sig <- getSignature
  return $ view $ whnf sig t

-- Errors
------------------------------------------------------------------------

data CheckError t v
    = ConstructorTypeError A.Expr (Type t v)
    | LambdaTypeError A.Expr (Type t v)
    | NotEqualityType (Type t v)
    | ExpectedFunctionType (Type t v) (Maybe A.Expr)
    | CannotInferTypeOf A.Expr
    | TermsNotEqual (Term t v) (Term t v)
    | SpineNotEqual (Type t v) [Elim t v] [Elim t v]
    | ExpectingRecordType (Type t v)
    | FreeVariableInEquatedTerm v
    | PatternMatchOnRecord A.Pattern
                           Name -- Record type constructor
    | MismatchingPattern (Type t v) A.Pattern

checkError :: (IsVar v, IsTerm t) => CheckError t v -> TC t v a
checkError = typeError . renderError
  where
    renderError (ConstructorTypeError synT type_) =
      "Constructor type error " ++ render synT ++ " : " ++ renderView type_
    renderError (NotEqualityType type_) =
      "Expecting an equality type: " ++ renderView type_
    renderError (LambdaTypeError synT type_) =
      "Lambda type error " ++ render synT ++ " : " ++ renderView type_
    renderError (ExpectedFunctionType type_ mbArg) =
      "Expected function type " ++ renderView type_ ++
      (case mbArg of
         Nothing  -> ""
         Just arg -> "\nIn application of " ++ render arg)
    renderError (CannotInferTypeOf synT) =
      "Cannot infer type of " ++ render synT
    renderError (TermsNotEqual t1 t2) =
      renderView t1 ++ "\n  !=\n" ++ renderView t2
    renderError (SpineNotEqual type_ es1 es2) =
      render es1 ++ "\n  !=\n" ++ render es2 ++ "\n  :\n" ++ renderView type_
    renderError (ExpectingRecordType type_) =
      "Expecting record type: " ++ renderView type_
    renderError (FreeVariableInEquatedTerm v) =
      "Free variable in term equated to metavariable application: " ++ renderVar v
    renderError (PatternMatchOnRecord synPat tyCon) =
      "Cannot have pattern " ++ render synPat ++ " for record type " ++ render tyCon
    renderError (MismatchingPattern type_ synPat) =
      render synPat ++ " does not match an element of type " ++ renderView type_

    renderVar = render . varName
