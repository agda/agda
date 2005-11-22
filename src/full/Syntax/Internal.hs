{-# OPTIONS -fglasgow-exts -fno-warn-incomplete-patterns #-}

{- Notes

  I intend to break the code at the bottom of this file into separate
  modules after I complete some basic functionality (reduction, and
  maybe equality). I am developing it in one file for the moment
  because it is far easier to see everyhting in front of me and I'm
  not yet sure how I want to break things up (and I don't want to
  hassle with moving files around the CVS repository).

  I am intentionally not writing catch-all cases for graceful internal
  error recovery. This can be done later after some testing and when
  there is a more concrete notion of how we'll handle errors.

-}

module Syntax.Internal where

--import Debug.Trace

import qualified Data.List as L
import Data.Generics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error

import Syntax.Common
import Syntax.Explanation
import Syntax.Position

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
--   **PJ: why is Expl last here and first in Abstract.hs
data Value = Var Nat                Expl
	   | App Value Value Hiding Expl
	   | Lam (Abs Value)        Expl
	   | Lit Literal            Expl
	   | Def QName              Expl 
	   | MetaV MId              Expl
  deriving (Typeable, Data, Show)

-- | this instance declaration is used in flex-flex unifier case
--
instance Eq Value where
    Var i _ == Var j _ = i == j
    v1      == v2      = False

var i   = Var i              Duh
lam m   = Lam (Abs noName m) Duh
app m n = App m n NotHidden  Duh
metaV x = MetaV x            Duh

addArgs :: [Value] -> GenericT
addArgs args = mkT addTrm `extT` addTyp where
    addTrm m = foldl app m args 
    addTyp a = case basicType a of
        MetaTBT x args' -> metaT (args'++args) x

data Type = El Value Sort      Expl
	  | Pi Type (Abs Type) Expl
	  | Sort Sort          Expl
	  | MetaT MId [Value]  Expl -- ^ list of dependencies for metavars
          | LamT (Abs Type)    Expl -- ^ abstraction needed for metavar dependency management
  deriving (Typeable, Data, Show)

pi a b = Pi a b              Duh
lamT a = LamT (Abs noName a) Duh
set0   = Sort (Type 0 Duh)   Duh
set n  = Sort (Type n Duh)   Duh
sort s = Sort s              Duh
metaT deps x = MetaT x deps  Duh

data Sort = Type Nat Expl
	  | Prop Expl
	  | MetaS MId Expl 
	  | Lub Sort Sort Expl
  deriving (Typeable, Data, Show)

prop    = Prop Duh
metaS x = MetaS x Duh

data Abs a = Abs Name a deriving (Typeable, Data, Show)
data Why   = Why        deriving (Typeable, Data, Show)

-- | Check if given term is an abstraction.
--
isAbs :: Data a => a -> Bool
isAbs x = dataTypeName (dataTypeOf x) == dataTypeName (dataTypeOf (Abs (Name noRange "") ()))

-- | Apply @f@ everywhere in a term, until told not to. 
--   Local reader state keeps track of how many binders have been passed.
--   Writer output lets @walk@ know whether to continue the traversal after
--     applying the function.
--   Might want to add some way to not traverse explanations (with something like 
--     @isabs@ above).
--
walk :: Monad m => GenericM (ReaderT Int (WriterT WalkDone m)) -> GenericM m
walk f x = do
    (v, _) <- runWriterT $ runReaderT (go f x) 0
    return v 
  where
    go :: Monad m => GenericM (ReaderT Int (WriterT WalkDone m)) -> 
                     GenericM (ReaderT Int (WriterT WalkDone m))
    go f x = do
        (v, continue) <- listen $ f x
        case continue of
            Done     -> return v
            Continue -> 
                if isAbs x then local (+ 1) $ gmapM (go f) v 
                                         else gmapM (go f) v

data WalkDone = Done | Continue 
instance Monoid WalkDone where
    mempty = Continue
    mappend Continue x        = x
    mappend Done     Continue = Done
    mappend Done     Done     = Done

-- | @endWalk@ is used, instead of @return@, by a traversal function 
--     which wants to stop the term traversal.
--   If traversal function wants to continue traversal, then @return@
--     is used instead.
--
endWalk :: Monad m => a -> ReaderT Int (WriterT WalkDone m) a
endWalk x = do
    tell Done
    return x


-- | Substitute @repl@ for @(Var 0 _)@ in @x@.
--
subst :: Value -> GenericT
subst repl x = runIdentity $ walk (mkM goVal) x where
  goVal (Var i expl) = do
      n <- ask
      endWalk $ if i == n then adjust n repl 
               else Var (if i > n then i - 1 else i) expl
  goVal x = return x

-- | Add @k@ to index of each open variable in @x@.
--
adjust :: Int -> GenericT
adjust k x = runIdentity $ walk (mkM goTm) x where
  goTm (Var i expl) = do
      n <- ask
      endWalk $ Var (if i >= n then i + k else i) expl
  goTm x = return x


-- | Basic view without explanations.
--
data BasicValue = VarBV Nat 
		| AppBV Value Value 
		| LamBV (Abs Value)
		| LitBV Literal 
		| DefBV QName 
		| MetaVBV MId
  deriving (Typeable, Data)

data BasicType = ElBT Value Sort
	       | PiBT Type (Abs Type)
	       | SortBT Sort
	       | MetaTBT MId [Value]
               | LamTBT (Abs Type)
  deriving (Typeable, Data)

data BasicSort = TypeBS Nat
	       | PropBS 
	       | MetaSBS MId
	       | LubBS Sort Sort
  deriving (Typeable, Data, Show)

basicValue :: Value -> BasicValue
basicValue v = case v of
    Var i       _ -> VarBV i
    App v1 v2 _ _ -> AppBV v1 v2
    Lam v       _ -> LamBV v
    Lit l       _ -> LitBV l
    Def f       _ -> DefBV f
    MetaV x     _ -> MetaVBV x

basicType :: Type -> BasicType
basicType a = case a of
    El v s       _ -> ElBT v s
    Pi a b       _ -> PiBT a b
    Sort s       _ -> SortBT s
    MetaT x deps _ -> MetaTBT x deps
    LamT a       _ -> LamTBT a
				  
basicSort :: Sort -> BasicSort
basicSort s = case s of
    Type n    _ -> TypeBS n
    Prop      _ -> PropBS
    MetaS x   _ -> MetaSBS x
    Lub s1 s2 _ -> LubBS s1 s2


-- | View as a spine, where head is always visible. 
--
data SpineValue = VarSV Nat [Value]
		| LamSV (Abs Value) [Value]
		| LitSV Literal -- ^ literals can't be applied
		| DefSV QName [Value]
		| MetaVSV MId [Value]
  deriving (Typeable, Data, Show)

spineValue :: Value -> SpineValue
spineValue v = app [] $ basicValue v where
    app args v = case v of
        VarBV i     -> VarSV i args
	AppBV v1 v2 -> app (v2 : args) (basicValue v1)
	LamBV v     -> LamSV v args
	LitBV l     -> case args of [] -> LitSV l
	DefBV f     -> DefSV f args
	MetaVBV x   -> MetaVSV x args


--------------------------------------------------------------
--
-- Stuff which might be better off in other files.
--
--------------------------------------------------------------

--
-- Monad
--
data TCState = TCSt {
  genSymSt :: Int,
  metaSt   :: Store,
  cnstrSt  :: Constraints,
  sigSt    :: Signature
} deriving Show

-- | Type Checking errors
--
data TCErr = Fatal String 
	   | Pattern MId -- ^ for pattern violations, carries involved metavar
  deriving Show

instance Error TCErr where
    noMsg = Fatal ""
    strMsg s = Fatal s
patternViolation mId = throwError $ Pattern mId

type TCErrMon = Either TCErr
type TCM a = StateT TCState (ReaderT Context TCErrMon) a

-- | get globally new symbol (@Int@)
--
genSym :: TCM Int
genSym = do
    v <- gets genSymSt
    modify (\st -> st{ genSymSt = v + 1})
    return v

-- | Generate [Var 0 Duh, Var 1 Duh, ...] for all declarations in context.
--   Used to make arguments for newly generated @Type@ metavars.
--
allCtxVars = do
    ctx <- ask
    return $ map var $ [0 .. length ctx - 1]
--    return $ snd $ L.mapAccumL (\n _ -> (n+1, var n)) 0 ctx

--
-- Constraints
--
type ConstraintId = Int

data Constraint = ValueEq Type Value Value
		| TypeEq Type Type
  deriving Show

-- | Catch pattern violation errors and adds a constraint.
--
catchConstr :: Constraint -> TCM () -> TCM ()
catchConstr cnstr v =
   catchError v (\ err -> case err of
       Pattern mId -> addCnstr [mId] cnstr
       _           -> throwError err
       )

type Constraints = [(ConstraintId,(Signature,Context,Constraint))]

-- | add a new constraint
--   first arg is a list of @MId@s which should wake-up the constraint
--
addCnstr :: [MId] -> Constraint -> TCM ()
addCnstr mIds c = do
    ctx <- ask
    sig <- gets sigSt
    cId <- genSym
    modify (\st -> st{
        cnstrSt = (cId,(sig,ctx,c)) : cnstrSt st,
        metaSt = map (addTrigger cId) $ metaSt st
        })        
  where
    addTrigger cId (id, mi) = 
      let mi' = if elem id mIds then case mi of
                    UnderScoreV a cIds -> UnderScoreV a $ cId : cIds
                    UnderScoreT s cIds -> UnderScoreT s $ cId : cIds
                    UnderScoreS cIds   -> UnderScoreS   $ cId : cIds
                    HoleV       a cIds -> HoleV a       $ cId : cIds
                    HoleT       s cIds -> HoleT s       $ cId : cIds
                else mi
      in (id, mi')

wakeup cId = do
    cnstrs <- gets cnstrSt
    case lookup cId cnstrs of
        Just (sig, ctx, ValueEq a m1 m2) -> go sig ctx $ equalVal Why a m1 m2
        Just (sig, ctx, TypeEq a1 a2)    -> go sig ctx $ equalTyp Why a1 a2
  where
    go sig ctx v = do
        sigCurrent <- gets sigSt
        modify (\st -> st{sigSt = sig})
        local (\_ -> ctx) v
        modify (\st -> st{sigSt = sigCurrent})

--
-- Meta Variables
--
type MId = Int

data MetaInfo = InstV Value
	      | InstT Type
              | InstS Sort
	      | UnderScoreV Type [ConstraintId]
	      | UnderScoreT Sort [ConstraintId]
	      | UnderScoreS      [ConstraintId]
	      | HoleV       Type [ConstraintId]
	      | HoleT       Sort [ConstraintId]
  deriving Show

type Store = [(MId, MetaInfo)]

getCIds (UnderScoreV _ cIds) = cIds
getCIds (UnderScoreT _ cIds) = cIds
getCIds (UnderScoreS   cIds) = cIds
getCIds (HoleV       _ cIds) = cIds
getCIds (HoleT       _ cIds) = cIds

setRef :: Data a => a -> MId -> MetaInfo -> TCM ()
setRef _ x v = do
    store <- gets metaSt
    let (cIds, store') = replace [] store
    mapM_ wakeup cIds
  where
    replace passed ((y,var):mIds) = 
        if x == y then (getCIds var, passed++((y,v):mIds)) 
        else replace (passed++[(y,var)]) mIds

-- | Generate new meta variable.
--   The @MetaInfo@ arg is meant to be either @UnderScore@X or @Hole@X.
--
newMeta :: (MId -> a) -> MetaInfo -> TCM a
newMeta meta initialVal = do
    x <- genSym
    modify (\st -> st{metaSt = (x, initialVal):(metaSt st)})
    return $ meta x

-- | Used to give an initial value to newMeta.  
--
getMeta :: MId -> TCM (MetaInfo)
getMeta x = do
    store <- gets metaSt
    deps <- allCtxVars -- !!! ok for generated type metavars below?
    case lookup x store of
        Just (UnderScoreV _ _) -> do
            s <- newMeta metaS $ UnderScoreS []
            a <- newMeta (metaT deps) $ UnderScoreT s [] -- !!! sketchy
            return $ (UnderScoreV a [])
        Just (UnderScoreT s _) -> return $ (UnderScoreT s [])
        Just (UnderScoreS _) -> return $ (UnderScoreS [])
        Just (HoleV a _) -> do
            s <- newMeta metaS $ UnderScoreS []
            a <- newMeta (metaT deps) $ UnderScoreT s [] -- !!! sketchy
            return $ (HoleV a [])
        Just (HoleT s _) -> return $ (HoleT s [])
          
-- | Generate new metavar of same kind (@Hole@X or @UnderScore@X) as that
--     pointed to by @MId@ arg.
--
newMetaSame :: MId -> (MId -> a) -> TCM a
newMetaSame x meta = do
    (v) <- getMeta x
    newMeta meta v

-- | instantiate a type 
--   results is open meta variable or a non meta variable type.
--
instType :: Type -> TCM Type
instType a = case basicType a of
    (MetaTBT x deps) -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstT a') -> instType $ reduceType a' deps
            Just _          -> return a
    _ -> return a

reduceType :: Type -> [Value] -> Type
reduceType a args = case basicType a of
    LamTBT (Abs _ a) -> reduceType (subst (head args) a) $ tail args
    _    | null args -> a

-- | instantiate a sort 
--   results is open meta variable or a non meta variable sort.
--
instSort :: Sort -> TCM Sort
instSort s = case basicSort s of
    (MetaSBS x) -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstS s') -> instSort s'
            Just _          -> return s
    _ -> return s

--
-- Context and Signature
--
type Context = [CtxElm]
type Signature = Context

data CtxElm = Decl Name Type (Maybe [Name]) -- ^ ind. types have list of constructors
	    | Defn Name [Clause]
	    | NameSpace Name Context
  deriving (Typeable, Data, Show)

isDecl ce = case ce of Decl _ _ _    -> True; _ -> False
isDefn ce = case ce of Defn _ _      -> True; _ -> False
isNmsp ce = case ce of NameSpace _ _ -> True; _ -> False

-- | add a declaration to the context
--
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a v = local ((Decl x a Nothing :) . adjust 1) v
    

-- | get type of bound variable (i.e. deBruijn index)
--
typeOfBV :: Nat -> TCM Type
typeOfBV n = do
    ctx <- ask
    case (filter isDecl ctx) !! n of
        Decl _ a _ -> return a

-- | get either type or definition of a constant. 
--   this navigates namespace structure and uses passed
--     function to find data after right namespace is reached
--
getConstInfoM :: (Signature -> Name -> a) -> QName -> TCM a
getConstInfoM fun c = do
    ctx <- ask  -- need to look here for local definitions
    sig <- gets sigSt 
    return $ getConstInfo fun (ctx++sig) c

getConstInfo :: (Signature -> Name -> a) -> Context -> QName -> a
getConstInfo fun ctx (Qual pkg name) = 
    case L.find (\ (NameSpace x _) -> x == pkg) (filter isNmsp ctx) of
        Just (NameSpace _ ctx') -> getConstInfo fun ctx' name
getConstInfo fun ctx (QName c) = fun ctx c

-- | get type of a constant 
--
typeOfConst :: QName -> TCM Type
typeOfConst = getConstInfoM find where
    find sig c = case L.find (\ (Decl x _ _) -> x == c) (filter isDecl sig) of
        Just (Decl _ a _) -> a


--
-- Definitions
--

-- | a clause is a list of patterns and a clause body
--   the number of binding patterns in a clause should
--     match the number of @Bind@s in the body
--
data Clause = Clause [Pattern] ClauseBody deriving (Typeable, Data, Show) 
data ClauseBody = Body Value 
		| Bind (Abs ClauseBody)
  deriving (Typeable, Data, Show)

-- | Patterns are variables, constructors, or wildcards.
--   @Name@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @Name@.
--
data Pattern = VarP Name
	     | ConP QName [Pattern]
             | WildP
  deriving (Typeable, Data, Show)


--
-- Reduction
--

-- | Reduce a value to head-normal form.
--   Taking this function out of the monad allows us to get
--     call-by-need semantics for free.
--   Arguments are not evaluated until just before being substituted.
--     So @reduce st ctx sig (c m1 m2) == c m1 m2@ when @c@ is an 
--     undefined constant.
--
reduce :: Store -> Context -> Signature -> Value -> Value
reduce store ctx sig v = go v where
    go v = case spineValue v of
        LamSV (Abs _ v') (arg:args) -> go $ addArgs args (subst (go arg) v')
        MetaVSV x args -> case lookup x store of
            Just (InstV v) -> go $ addArgs args v
            Just _         -> v
        DefSV f args -> case defOfConst f of
            []                    -> v -- no definition for head
            cls@(Clause ps _ : _) -> 
                if length ps == length args then appDef v cls args
                else if length ps > length args then
                    let (args1,args2) = splitAt (length ps) args 
                    in go $ addArgs args2 (appDef v cls args1)
                else v -- partial application
        _ -> v

    -- | get definition of a constant (i.e. a list of clauses)
    --
    defOfConst :: QName -> [Clause]
    defOfConst = getConstInfo find (ctx++sig) where
        find sig c = case L.find (\ (Defn x _) -> x == c) (filter isDefn sig) of
            Just (Defn _ cls) -> cls

    -- | Apply a defined function to it's arguments.
    --   First arg is original value which is needed in case no clause matches.
    --
    appDef :: Value -> [Clause] -> [Value] -> Value
    appDef v cls args = goCls cls args where
        goCls [] _ = v -- no clause matched, can happen with parameter arguments
        goCls (cl@(Clause pats body) : cls) args =
            case matchPats [] pats args of
                Just args' -> app args' body
                Nothing -> goCls cls args
        app [] (Body v') = go v'
        app (arg : args) (Bind (Abs _ body)) = app args $ subst (go arg) body
	

    -- | Match the given patterns to the given arguments.
    --   Returns updated list of values to instantiate the
    --     bound variables in the patterns.
    --
    matchPats :: [Value] -> [Pattern] -> [Value] -> Maybe [Value]
    matchPats curArgs (pat:pats) (arg:args) = do
        newArgs <- matchPat curArgs pat arg 
        matchPats newArgs pats args
    matchPats curArgs [] [] = Just curArgs

    matchPat :: [Value] -> Pattern -> Value -> Maybe [Value]
    matchPat curArgs WildP _ = Just curArgs
    matchPat curArgs (VarP x) arg = Just $ curArgs++[arg]
    matchPat curArgs (ConP c pats) arg =  
        case spineValue $ go arg of 
            DefSV c' args | c' == c -> matchPats curArgs pats args 
            _ -> Nothing


-- | Monadic version of reduce.
--
reduceM :: Value -> TCM Value
reduceM v = do
    store <- gets metaSt
    ctx   <- ask
    sig   <- gets sigSt
    return $ reduce store ctx sig v


-- | View as a reduced spine, where head is always visible.
--   If head is a meta variable, then that variable is open.
--
data WhnfValue = VarWV Nat [Value]
                | LamWV (Abs Value)
                | LitWV Literal -- literals can't be applied
                | DefWV QName [Value]
                | MetaVWV MId [Value] -- MId shouldn't be instantiated
  deriving (Typeable, Data, Show)

whnfValue :: Value -> TCM WhnfValue
whnfValue v = do 
    v' <- reduceM v
    return $ case spineValue v' of
        VarSV i args   -> VarWV i args
        LitSV c        -> LitWV c
        LamSV v []     -> LamWV v
        DefSV f args   -> DefWV f args
        MetaVSV x args -> MetaVWV x args


-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are unique @Var@s and returns the
--     list of corresponding indices for each arg; this is done
--     to not define equality on @Value@.
--
checkArgs :: MId -> [Value] -> TCM [Int]
checkArgs x args = go [] args where
    go ids  []           = return ids
    go done (arg : args) = case basicValue arg of 
        VarBV i | not $ elem i done -> go (i:done) args
        _                           -> patternViolation x 

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
findIdx :: (Eq a, Monad m) => [a] -> a -> m Int
findIdx vs v = go 0 vs where
    go i (v' : vs) | v' == v = return i
    go i (_  : vs)           = go (i + 1) vs
    go _ []                  = fail "findIdx"

abstract :: [Value] -> GenericT
abstract args = mkT absV `extT` absT where
    absV v = foldl (\v _ -> lam v ) v args
    absT a = foldl (\a _ -> lamT a) a args 

-- | Extended occurs check
--
occ :: MId -> [Int] -> GenericM TCM
occ y okVars v = go v where
    go v = walk (mkM occVal) v --`extM` occTyp
    occVar inst meta x args =
        if x == y then fail "occ"
        else do
            (args', newArgs) <- occVarArgs x args
            if length args' == length newArgs
                then return ()
                else lift $ lift $ do
                    v1 <-  newMetaSame x meta
                    setRef Why x $ inst $ abstract args (addArgs newArgs v1)
            endWalk $ addArgs args' (meta x)
    occVarArgs x args = ocA ([],[]) [] 0 args where
        ocA res _ _ [] = return res
        ocA (old, new) ids idx (arg:args) = do
            v <- lift $ lift $ whnfValue arg
            case v of
                VarWV i [] | not $ elem i ids -> 
                    case findIdx okVars i of
                        Just j -> ocA (old++[var j], new++[var idx]) (i:ids) (idx+1) args
                        Nothing -> ocA (old++[arg], new) ids (idx+1) args
                _ -> patternViolation x
    occVal v = do
        v' <- lift $ lift $ whnfValue v -- would spineValue work here or not? 
        case v' of 
            VarWV i args -> do
                j <- findIdx okVars i
                args' <- mapM occVal args -- necessary because addArgs returns @Value@
                endWalk $ addArgs args' (var j)
            MetaVWV x args -> occVar InstV metaV x args
    occTyp v = do
        v' <- lift $ lift $ instType v
        case basicType v' of
           MetaTBT x args -> occVar (InstT) (metaT []) x args
           _ -> return v'
           
        
-- | Assign to an open metavar.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
assign :: MId -> [Value] -> GenericQ (TCM ())
assign x args = mkQ (fail "assign") (ass InstV) `extQ` (ass InstT) where
    ass :: Data a => (a -> MetaInfo) -> a -> TCM ()
    ass inst v = do
        ids <- checkArgs x args
        v' <- occ x ids v    
        setRef Why x $ inst v'


-- | Equality of two instances of the same metavar
--
equalSameVar :: Data a => 
                (MId -> a) -> (a -> MetaInfo) -> MId -> [Value] -> [Value] -> TCM ()
equalSameVar meta inst x args1 args2 =
    if length args1 == length args2 then do
        -- next 2 checks could probably be nicely merged into construction 
        --   of newArgs using ListT, but then can't use list comprehension.
        checkArgs x args1 
        checkArgs x args2 
        let idx = [0 .. length args1 - 1]
        let newArgs = [var n | (n, (a,b)) <- zip idx $ zip args1 args2, a == b]
        v <- newMetaSame x meta
        setRef Why x $ inst $ abstract args1 (addArgs newArgs v)
    else fail $ "equalSameVar"


-- | Type directed equality on values.
--
equalVal :: Data a => a -> Type -> Value -> Value -> TCM ()
equalVal _ a m n = do
    a' <- instType a
    case basicType a' of
        PiBT a (Abs name b) -> 
            let p = var 0
                m' = adjust 1 m
                n' = adjust 1 n
            in addCtx name a $ equalVal Why b (app m' p) (app n' p)
        MetaTBT x _ -> addCnstr [x] (ValueEq a m n)
        _ -> catchConstr (ValueEq a' m n) $ equalAtm Why m n

-- | Syntax directed equality on atomic values
--
equalAtm :: Data a => a -> Value -> Value -> TCM ()
equalAtm _ m n = do
    mVal <- reduceM m  -- need mVal for the metavar case
    nVal <- reduceM n  -- need nVal for the metavar case
    case (spineValue mVal, spineValue nVal) of
        (LitSV l1, LitSV l2) | l1 == l2 -> return ()
        (VarSV i iArgs, VarSV j jArgs) | i == j -> do
            a <- typeOfBV i
            equalArg Why a iArgs jArgs
        (DefSV x xArgs, DefSV y yArgs) | x == y -> do
            a <- typeOfConst x
            equalArg Why a xArgs yArgs
        (MetaVSV x xArgs, MetaVSV y yArgs) | x == y -> equalSameVar metaV InstV x xArgs yArgs
        (MetaVSV x xArgs, _) -> assign x xArgs nVal
        (_, MetaVSV x xArgs) -> assign x xArgs mVal
        _ -> fail $ "equalAtm "++(show m)++" "++(show n)


-- | Type-directed equality on argument lists
--
equalArg :: Data a => a -> Type -> [Value] -> [Value] -> TCM ()
equalArg _ a args1 args2 = do
    a' <- instType a
    case (basicType a', args1, args2) of 
        (_, [], []) -> return ()
        (PiBT b (Abs _ c), (arg1 : args1), (arg2 : args2)) -> do
            equalVal Why b arg1 arg2
            equalArg Why (subst arg1 c) args1 args2
        _ -> fail $ "equalArg "++(show a)++" "++(show args1)++" "++(show args2)


-- | Equality on Types
--   Assumes @Type@s being compared are at the same @Sort@
--   !!! Safe to not have @LamT@ case? @LamT@s shouldn't surface?
--
equalTyp :: Data a => a -> Type -> Type -> TCM ()
equalTyp _ a1 a2 = do
    a1' <- instType a1
    a2' <- instType a2
    case (basicType a1', basicType a2') of
        (ElBT m1 s1, ElBT m2 s2) ->
            equalVal Why (sort s1) m1 m2
        (PiBT a1 (Abs name a2), PiBT b1 (Abs _ b2)) -> do
            equalTyp Why a1 b1
            addCtx name a1 $ equalTyp Why (subst (var 0) a2) (subst (var 0) b2)
        (SortBT s1, SortBT s2) -> return ()
        (MetaTBT x xDeps, MetaTBT y yDeps) | x == y -> 
            equalSameVar (metaT []) InstT x xDeps yDeps
        (MetaTBT x xDeps, a) -> assign x xDeps a 
        (a, MetaTBT x xDeps) -> assign x xDeps a 


---------------------------------------------------------------------------
--
-- Example
--
test x = runReaderT (runStateT x testSt{sigSt = []}) []

newmetaT = newMeta (metaT []) $ UnderScoreT prop []
newmetaV = newMeta metaV $ UnderScoreV set0 []
eqTest = do
    x <- newmetaV
    equalVal Why set0 x x
    
   

testRed v = runReaderT (evalStateT (reduceM v) testSt) []

normalize :: GenericM TCM
normalize v = walk (mkM (\v -> lift $ lift  $ reduceM v)) v
testNrm v = runReaderT (evalStateT (normalize v) testSt) []

testSt = TCSt {
  genSymSt = 0,
  metaSt   = [],
  cnstrSt  = [],
  sigSt    = testSig
 }

testSig = [

  -- nat : set_0
  Decl (Name noRange "nat") (Sort (Type 0 Duh) Duh) 
    (Just [Name noRange "Z", Name noRange "S"]),

  -- Z : nat
  Decl (Name noRange "Z") (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) 
    Nothing,
  Defn (Name noRange "Z") [],

  -- S : nat -> nat
  Decl (Name noRange "S") (
    Pi (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) 
       (Abs (Name noRange "_") $ El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) 
       Duh 
  ) Nothing,
  Defn (Name noRange "S") [],

  -- plus : nat -> nat -> nat
  Decl (Name noRange "plus") (
    Pi (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) (Abs (Name noRange "_") $
    Pi (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) (Abs (Name noRange "_") $
    El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) Duh) Duh 
  ) Nothing,

  Defn (Name noRange "plus") [ 

    -- plus Z n = n
    Clause [ConP (QName $ Name noRange "Z") [], VarP $ Name noRange "n"] $ 
      Bind $ Abs (Name noRange "n") $ Body $ Var 0 Duh,

    -- plus (S m) n = S (plus m n)
    Clause 
      [ConP (QName $ Name noRange "S") [VarP $ Name noRange "m"], VarP $ Name noRange "n"] $ 
      Bind $ Abs (Name noRange "m") $ Bind $ Abs (Name noRange "n") $ 
      Body $ 
        App (Def (QName $ Name noRange "S") Duh) 
            (App (App (Def (QName $ Name noRange "plus") Duh) (Var 1 Duh) NotHidden Duh) 
                 (Var 0 Duh) 
                 NotHidden 
                 Duh 
            )
            NotHidden 
            Duh
  ]
 ]

s = Def (QName $ Name noRange "S") Duh
z = Def (QName $ Name noRange "Z") Duh
plus = Def (QName $ Name noRange "plus") Duh

two = app s (app s z)
three = app s (app s (app s z))


