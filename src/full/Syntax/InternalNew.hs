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

module Syntax.InternalNew where

import Debug.Trace

import qualified Data.List as L
import Data.Generics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error

import Syntax.Common
import Syntax.Position


-- ! Type of argument lists. Might want to later add hidden info...
--
type Args = [Value]

args2str hd [] = return hd
args2str hd (arg:args) = do
    a <- val2str arg
    args2str (hd++(if a == "" then "" else " "++a)) args

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
data Value = Var Nat Args
	   | Lam (Abs Value) Args -- ^ allow for redexes
	   | Lit Literal
	   | Def QName Args
	   | MetaV MId Args
  deriving (Typeable, Data)

val2str (Var i args) = do
    n <- ask
    args2str (if n > i then "x"++(show $ n - i) else "p"++(show $ i - n)) args
val2str (Lam (Abs _ v) args) = do
    hd <- local (+ 1) $ val2str v
    n <- ask
    args2str ("(x"++(show $ n + 1)++" \\ "++hd++")") args
val2str (Lit l) = return $ show l
val2str (Def c args) = args2str (show c) args
val2str (MetaV x args) = args2str ("?"++(show x)) args

instance Show Value where show v = runReader (val2str v) 0

-- | this instance declaration is used in flex-flex unifier case
--
instance Eq Value where
    Var i [] == Var j [] = i == j
    v1       == v2       = False

data Type = El Value Sort     
	  | Pi Type (Abs Type)
	  | Sort Sort         
	  | MetaT MId Args  -- ^ list of dependencies for metavars
          | LamT (Abs Type) -- ^ abstraction needed for metavar dependency management, !!! is a type necessary?
  deriving (Typeable, Data)

typ2str (El v _) = val2str v
typ2str (Pi a (Abs _ b)) = do
    aStr <- typ2str a
    bStr <- local (+ 1) $ typ2str b
    n <- ask
    return $ "{x"++(show $ n + 1)++" : "++aStr++"} "++bStr
typ2str (Sort s) = return $ srt2str s
typ2str (MetaT x args) = args2str ("?"++(show x)) args
typ2str (LamT (Abs _ a)) = do
    aStr <- local (+ 1) $ typ2str a
    n <- ask
    return $ "[x"++(show $ n + 1)++"] "++aStr

instance Show Type where show a = runReader (typ2str a) 0

set0   = Sort (Type 0)
set n  = Sort (Type n)
sort s = Sort s       

addArgs :: Args -> GenericT
addArgs args = mkT addTrm `extT` addTyp where
    addTrm m = case m of
        Var i args' -> Var i (args'++args)
        Lam m args' -> Lam m (args'++args)
        Def c args' -> Def c (args'++args)
        MetaV x args' -> MetaV x (args'++args) 
    addTyp a = case a of
        MetaT x args' -> MetaT x (args'++args)

data Sort = Type Nat
	  | Prop 
	  | MetaS MId 
	  | Lub Sort Sort 
  deriving (Typeable, Data)

srt2str (Type n) = "set"++(show n)
srt2str Prop = "prop"
srt2str (MetaS x) = "?"++(show x)
srt2str (Lub s1 s2) = (srt2str s1)++" \\/ "++(srt2str s2)

instance Show Sort where show = srt2str

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
endWalk x = do tell Done; return x


-- | Substitute @repl@ for @(Var 0 _)@ in @x@.
--
subst :: Value -> GenericT
subst repl x = runIdentity $ walk (mkM goVal) x where
  goVal (Var i args) = do
      n <- ask
      if i == n 
          then do 
              args' <- mapM goVal args
              endWalk $ addArgs args' $ adjust n repl 
          else return $ Var (if i > n then i - 1 else i) args
  goVal x = return x

-- | Add @k@ to index of each open variable in @x@.
--
adjust :: Int -> GenericT
adjust k x = runIdentity $ walk (mkM goTm) x where
  goTm (Var i args) = do
      n <- ask
      return $ Var (if i >= n then i + k else i) args
  goTm x = return x


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
}

instance Show TCState where 
    show st = 
        "{genSymSt="++(show $ genSymSt st)++
        ", metaSt="++(show $ map StoreElm $ metaSt st)++
        ", cnstrSt="++(show $ cnstrSt st)++
        ", sigSt="++(show $ sigSt st)++
        "}"

-- | Type Checking errors
--
data TCErr = Fatal String 
	   | PatternErr MId -- ^ for pattern violations, carries involved metavar
  deriving Show

instance Error TCErr where
    noMsg = Fatal ""
    strMsg s = Fatal s
patternViolation mId = throwError $ PatternErr mId

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
allCtxVars :: TCM Args
allCtxVars = do
    ctx <- ask
    return $ map (\i -> Var i []) $ [0 .. length ctx - 1]

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
       PatternErr mId -> addCnstr mId cnstr
       _           -> throwError err
       )

type Constraints = [(ConstraintId,(Signature,Context,Constraint))]

-- | add a new constraint
--   first arg is a list of @MId@s which should wake-up the constraint
--
addCnstr :: MId -> Constraint -> TCM ()
addCnstr mId c = do
    ctx <- ask
    sig <- gets sigSt
    cId <- genSym
    modify (\st -> st{
        cnstrSt = (cId,(sig,ctx,c)) : cnstrSt st,
        metaSt = map (addTrigger cId) $ metaSt st
        })        
  where
    addTrigger cId (id, mInfo) =  (id, if id == mId then addCId cId mInfo else mInfo)

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

data MetaVariable = InstV Value
                  | InstT Type
                  | InstS Sort
                  | UnderScoreV Type [ConstraintId]
                  | UnderScoreT Sort [ConstraintId]
                  | UnderScoreS      [ConstraintId]
                  | HoleV       Type [ConstraintId]
                  | HoleT       Sort [ConstraintId]
  deriving Show

applyStore = do
    st <- gets metaSt
    st' <- mapM apply st
    modify (\x -> x{metaSt= st'})
  where
    apply (x, InstV v) = do v' <- normalize v; return (x, InstV v')
    apply (x, InstT a) = do a' <- instType a; return (x, InstT a')
    apply x = return x

newtype StoreElm = StoreElm (MId, MetaVariable)
instance Show StoreElm where show (StoreElm x) = storeElm2str x
storeElm2str (x, mv) = "?"++(show x)++(case mv of
    InstV v -> ":="++(show v)
    InstT a -> ":="++(show a)
    UnderScoreV a cIds -> ":"++(show a)++"|"++(show cIds)
    UnderScoreT s cIds -> ":"++(show s)++"|"++(show cIds)
    UnderScoreS cIds -> "|"++(show cIds)
    HoleV a cIds -> ":"++(show a)++"|"++(show cIds)
    HoleT s cIds -> ":"++(show s)++"|"++(show cIds)
  )

type Store = [(MId, MetaVariable)]

getCIds (UnderScoreV _ cIds) = cIds
getCIds (UnderScoreT _ cIds) = cIds
getCIds (UnderScoreS   cIds) = cIds
getCIds (HoleV       _ cIds) = cIds
getCIds (HoleT       _ cIds) = cIds

addCId cId mInfo = case mInfo of
    UnderScoreV a cIds -> UnderScoreV a $ cId : cIds
    UnderScoreT s cIds -> UnderScoreT s $ cId : cIds
    UnderScoreS cIds   -> UnderScoreS   $ cId : cIds
    HoleV       a cIds -> HoleV a       $ cId : cIds
    HoleT       s cIds -> HoleT s       $ cId : cIds

setRef :: Data a => a -> MId -> MetaVariable -> TCM ()
setRef _ x v = do
    store <- gets metaSt
    let (cIds, store') = replace [] store
    modify (\st -> st{metaSt = store'})
    mapM_ wakeup cIds
  where
    replace passed ((y,var):mIds) = 
        if x == y then (getCIds var, passed++((y,v):mIds)) 
        else replace (passed++[(y,var)]) mIds

-- | Generate new meta variable.
--   The @MetaVariable@ arg (2nd arg) is meant to be either @UnderScore@X or @Hole@X.
--
newMeta :: (MId -> a) -> MetaVariable -> TCM a
newMeta meta initialVal = do
    x <- genSym
    modify (\st -> st{metaSt = (x, initialVal):(metaSt st)})
    return $ meta x

-- | Used to give an initial value to newMeta.  
--   The constraint list will be filled-in as needed during assignment.
--
getMeta :: MId -> Args -> TCM (MetaVariable)
getMeta x args = do
    store <- gets metaSt
    case lookup x store of
        Just (UnderScoreV _ _) -> do
            s <- newMeta MetaS $ UnderScoreS []
            a <- newMeta (\x -> MetaT x args) $ UnderScoreT s [] 
            return $ (UnderScoreV a [])
        Just (UnderScoreT s _) -> return $ (UnderScoreT s [])
        Just (UnderScoreS _) -> return $ (UnderScoreS [])
        Just (HoleV a _) -> do
            s <- newMeta MetaS $ UnderScoreS []
            a <- newMeta (\x -> MetaT x args) $ UnderScoreT s [] 
            return $ (HoleV a [])
        Just (HoleT s _) -> return $ (HoleT s [])
          
-- | Generate new metavar of same kind (@Hole@X or @UnderScore@X) as that
--     pointed to by @MId@ arg.
--
newMetaSame :: MId -> Args -> (MId -> a) -> TCM a
newMetaSame x args meta = do
    (v) <- getMeta x args
    newMeta meta v

-- | instantiate a type 
--   results is open meta variable or a non meta variable type.
--
instType :: Type -> TCM Type
instType a = case a of
    (MetaT x args) -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstT a') -> instType $ reduceType a' args
            Just _          -> return a
    _ -> return a

reduceType :: Type -> [Value] -> Type
reduceType a args = case a of
    LamT (Abs _ a) -> reduceType (subst (head args) a) $ tail args
    _    | null args -> a

-- | instantiate a sort 
--   results is open meta variable or a non meta variable sort.
--
instSort :: Sort -> TCM Sort
instSort s = case s of
    (MetaS x) -> do 
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
--   @QName@ is used in @ConP@ rather than @Name@ since
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
    go v = case v of
        Lam (Abs _ v') (arg:args) -> go $ addArgs args (subst (go arg) v')
        MetaV x args -> case lookup x store of
            Just (InstV v) -> go $ addArgs args v
            Just _ -> v
        Def f args -> case defOfConst f of
            [] -> v -- no definition for head
            cls@(Clause ps _ : _) -> 
                if length ps == length args then appDef v cls args
                else if length ps < length args then
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
        case go arg of 
            Def c' args | c' == c -> matchPats curArgs pats args 
            _ -> Nothing


-- | Monadic version of reduce.
--
reduceM :: Value -> TCM Value
reduceM v = do
    store <- gets metaSt
    ctx   <- ask
    sig   <- gets sigSt
    return $ reduce store ctx sig v


-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are unique @Var@s and returns the
--     list of corresponding indices for each arg-- done
--     to not define equality on @Value@.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
--
checkArgs :: MId -> [Value] -> TCM [Int]
checkArgs x args = go [] args where
    go ids  []           = return $ reverse ids
    go done (arg : args) = case arg of 
        Var i [] | not $ elem i done -> go (i:done) args
        _                         -> patternViolation x 

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over this list @vs@.
--
findIdx :: (Eq a, Monad m) => [a] -> a -> m Int
findIdx vs v = go 0 (reverse vs) where
    go i (v' : vs) | v' == v = return i
    go i (_  : vs)           = go (i + 1) vs
    go _ []                  = fail "findIdx"

abstract :: [Value] -> GenericT
abstract args = mkT absV `extT` absT where
    absV v = foldl (\v _ -> Lam  (Abs noName v) []) v args
    absT a = foldl (\a _ -> LamT (Abs noName a)   ) a args 

-- | Extended occurs check
--
occ :: MId -> [Int] -> GenericM TCM
occ y okVars v = go v where
    go v = walk (mkM occVal) v --`extM` occTyp
    occMVar inst meta x args =
        if x == y then fail "occ"
        else do
            (args', newArgs) <- occMVarArgs x args
            trace ("occMVar: okVars="++(show okVars)++", args="++(show args)++", args'="++(show args')++", newArgs="++(show newArgs)++"\n") $ if length args' == length newArgs
                then return ()
                else lift $ lift $ do
                    v1 <-  newMetaSame x args meta -- !!! is args right here?
                    trace ("occMVar prune: v1="++(show v1)++"\n") $ setRef Why x $ inst $ abstract args (addArgs newArgs v1)
            endWalk $ addArgs args' (meta x)
    occMVarArgs x args = ocA ([],[]) [] (length args - 1) args where
        ocA res _ _ [] = return res
        ocA (old, new) ids idx (arg:args) = do
            v <- lift $ lift $ reduceM arg
            case v of
                Var i [] | not $ elem i ids -> 
                    trace ("occMVarArgs: findIdx "++(show okVars)++" "++(show i)++" = "++(show $ (findIdx okVars i:: Maybe Int))++"\n") $ case findIdx okVars i of
                        Just j -> ocA (old++[Var j []], new++[Var idx []]) (i:ids) (idx-1) args
                        Nothing -> ocA (old++[arg], new) ids (idx-1) args
                _ -> patternViolation x
    occVal v = do
        v' <- lift $ lift $ reduceM v 
        case v' of 
            Var i args -> do
                j <- findIdx okVars i
                return $ addArgs args (Var j []) -- continues walking along args
            MetaV x args -> occMVar InstV (\x -> MetaV x []) x args -- !!! MetaV should have no args?
            _ -> return v'
    occTyp v = do
        v' <- lift $ lift $ instType v
        case v' of
           MetaT x args -> occMVar (InstT) (\x -> MetaT x []) x args -- !!! MetaT should have no args?
           _ -> return v'
           
        
-- | Assign to an open metavar.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
assign :: MId -> [Value] -> GenericQ (TCM ())
assign x args = mkQ (fail "assign") (ass InstV) `extQ` (ass InstT) where
    ass :: (Show a, Data a) => (a -> MetaVariable) -> a -> TCM ()
    ass inst v = do
        ids <- checkArgs x args
        v' <- occ x ids v    
        trace ("assign: args="++(show args)++", v'="++(show v')++"\n") $ setRef Why x $ inst $ abstract args v'


-- | Equality of two instances of the same metavar
--
equalSameVar :: Data a => 
                (MId -> a) -> (a -> MetaVariable) -> MId -> [Value] -> [Value] -> TCM ()
equalSameVar meta inst x args1 args2 =
    if length args1 == length args2 then do
        -- next 2 checks could probably be nicely merged into construction 
        --   of newArgs using ListT, but then can't use list comprehension.
        checkArgs x args1 
        checkArgs x args2 
        let idx = [0 .. length args1 - 1]
        let newArgs = [Var n [] | (n, (a,b)) <- zip idx $ zip args1 args2, a == b]
        v <- newMetaSame x args1 meta -- !!! is args1 right here?
        setRef Why x $ inst $ abstract args1 (addArgs newArgs v)
    else fail $ "equalSameVar"


-- | Type directed equality on values.
--
equalVal :: Data a => a -> Type -> Value -> Value -> TCM ()
equalVal _ a m n = trace ("equalVal ("++(show a)++") ("++(show m)++") ("++(show n)++")\n") $ do
    a' <- instType a
    case a' of
        Pi a (Abs name b) -> 
            let p = Var 0 []
                m' = adjust 1 m
                n' = adjust 1 n
            in addCtx name a $ equalVal Why b (addArgs [p] m') (addArgs [p] n')
        MetaT x _ -> addCnstr x (ValueEq a m n)
        _ -> catchConstr (ValueEq a' m n) $ equalAtm Why m n

-- | Syntax directed equality on atomic values
--
equalAtm :: Data a => a -> Value -> Value -> TCM ()
equalAtm _ m n = do
    mVal <- reduceM m  -- need mVal for the metavar case
    nVal <- reduceM n  -- need nVal for the metavar case
    trace ("equalAtm ("++(show mVal)++") ("++(show nVal)++")\n") $ case (mVal, nVal) of
        (Lit l1, Lit l2) | l1 == l2 -> return ()
        (Var i iArgs, Var j jArgs) | i == j -> do
            a <- typeOfBV i
            equalArg Why a iArgs jArgs
        (Def x xArgs, Def y yArgs) | x == y -> do
            a <- typeOfConst x
            equalArg Why a xArgs yArgs
        (MetaV x xArgs, MetaV y yArgs) | x == y -> equalSameVar (\x -> MetaV x []) InstV x xArgs yArgs -- !!! MetaV args???
        (MetaV x xArgs, _) -> assign x xArgs nVal
        (_, MetaV x xArgs) -> assign x xArgs mVal
        _ -> fail $ "equalAtm "++(show m)++" ==/== "++(show n)


-- | Type-directed equality on argument lists
--
equalArg :: Data a => a -> Type -> [Value] -> [Value] -> TCM ()
equalArg _ a args1 args2 = do
    a' <- instType a
    case (a', args1, args2) of 
        (_, [], []) -> return ()
        (Pi b (Abs _ c), (arg1 : args1), (arg2 : args2)) -> do
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
    case (a1', a2') of
        (El m1 s1, El m2 s2) ->
            equalVal Why (sort s1) m1 m2
        (Pi a1 (Abs name a2), Pi b1 (Abs _ b2)) -> do
            equalTyp Why a1 b1
            addCtx name a1 $ equalTyp Why (subst (Var 0 []) a2) (subst (Var 0 []) b2)
        (Sort s1, Sort s2) -> return ()
        (MetaT x xDeps, MetaT y yDeps) | x == y -> 
            equalSameVar (\x -> MetaT x []) InstT x xDeps yDeps -- !!! MetaT???
        (MetaT x xDeps, a) -> assign x xDeps a 
        (a, MetaT x xDeps) -> assign x xDeps a 


---------------------------------------------------------------------------
--
-- Example
--
test x = runReaderT (runStateT (do x; applyStore) testSt{sigSt = []}) []

newmetaT = newMeta (\x -> MetaT x []) $ UnderScoreT Prop []
newmetaV = newMeta (\x -> MetaV x []) $ UnderScoreV set0 []
eqTest = do
    x <- newmetaV
    equalVal Why set0 x x
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 set0) (lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                            (lam $ lam $ app (app y $ Var 0 []) $ Var 1 [])
eqTest1 = do
    x <- newmetaV
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 set0) (lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                            (lam $ app y $ Var 0 [])
eqTest2 = do
    x <- newmetaV
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 set0) (lam $ app y $ Var 0 [])
                                            (lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])

eqTest3 = do
    x <- newmetaV
    equalVal Why (arr set0 $ arr set0 $ arr set0 set0) (lam $ lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                                       (lam $ lam $ lam $ app (app x $ Var 1 []) $ Var 2 [])

eqTest4 = do
    x <- newmetaV
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 $ arr set0 set0) (lam $ lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                                       (lam $ lam $ lam $ app (app y $ Var 1 []) $ Var 2 [])

lam v = Lam (Abs noName v) []
app x y = addArgs [y] x
arr x y = Pi x $ Abs noName y
   

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
  Decl (Name noRange "nat") (Sort (Type 0)) 
    (Just [Name noRange "Z", Name noRange "S"]),

  -- Z : nat
  Decl (Name noRange "Z") (El (Def (QName $ Name noRange "nat") []) (Type 0)) 
    Nothing,
  Defn (Name noRange "Z") [],

  -- S : nat -> nat
  Decl (Name noRange "S") (
    Pi (El (Def (QName $ Name noRange "nat") []) (Type 0)) 
       (Abs (Name noRange "_") $ El (Def (QName $ Name noRange "nat") []) (Type 0)) 
       
  ) Nothing,
  Defn (Name noRange "S") [],

  -- plus : nat -> nat -> nat
  Decl (Name noRange "plus") (
    Pi (El (Def (QName $ Name noRange "nat") []) (Type 0)) (Abs (Name noRange "_") $
    Pi (El (Def (QName $ Name noRange "nat") []) (Type 0)) (Abs (Name noRange "_") $
    El (Def (QName $ Name noRange "nat") []) (Type 0))) 
  ) Nothing,

  Defn (Name noRange "plus") [ 

    -- plus Z n = n
    Clause [ConP (QName $ Name noRange "Z") [], VarP $ Name noRange "n"] $ 
      Bind $ Abs (Name noRange "n") $ Body $ Var 0 [],

    -- plus (S m) n = S (plus m n)
    Clause 
      [ConP (QName $ Name noRange "S") [VarP $ Name noRange "m"], VarP $ Name noRange "n"] $ 
      Bind $ Abs (Name noRange "m") $ Bind $ Abs (Name noRange "n") $ 
      Body $ 
        Def (QName $ Name noRange "S") [Def (QName $ Name noRange "plus") [Var 1 [], Var 0 []]] 
  ]
 ]

s = Def (QName $ Name noRange "S")
z = Def (QName $ Name noRange "Z") []
plus = Def (QName $ Name noRange "plus")

two = s [s [z]]
three = s [s [s [z]]]


