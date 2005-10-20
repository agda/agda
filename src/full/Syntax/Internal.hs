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
data Value = Var Nat Expl
	   | App Value Value Hiding Expl
	   | Lam Type (Abs Value) Expl
	   | Lit Literal Expl
	   | Def QName Expl 
	   | MetaV MId Expl
  deriving (Typeable, Data, Show)

var i = Var i Duh
lam a m = Lam a (Abs noName m) Duh
app m n = App m n NotHidden Duh
addArgs = foldl app 

data Type = El Value Sort Expl
	  | Pi Type (Abs Type) Expl
	  | Sort Sort Expl
	  | MetaT MId Expl
  deriving (Typeable, Data, Show)

set0 = Sort (Type 0 Duh) Duh

data Sort = Type Nat Expl
	  | Prop Expl
	  | MetaS MId Expl 
	  | Lub Sort Sort Expl
  deriving (Typeable, Data, Show)

data Abs a = Abs Name a deriving (Typeable, Data, Show)

-- | Check if given term is an abstraction.
--
isAbs x = dataTypeName (dataTypeOf x) == dataTypeName (dataTypeOf (Abs (Name noRange "") ()))

-- | Apply @f@ everywhere in a term, 
--   Local reader state keeps track of how many binders have been passed.
--   Might want to add some way to not traverse explanations.
--
walk :: Monad m => GenericM (ReaderT Int m) -> GenericM (ReaderT Int m)
walk f x = do
    x' <- f x
    if isAbs x then local (+ 1) $ gmapM (walk f) x' else gmapM (walk f) x'

walkTarg :: Monad m => GenericQ Bool -> GenericM (ReaderT Int m) -> GenericM (ReaderT Int m)
walkTarg isTarg f x = 
    if isTarg x then f x else
        if isAbs x then local (+ 1) $ gmapM (walk f) x else gmapM (walk f) x


-- | Substitute @repl@ for @(Var 0 _)@ in @x@.
--
subst :: Value -> GenericT
subst repl x = runIdentity $ runReaderT (walk (mkM goVal) x) 0 where
  goVal (Var i expl) = do
      n <- ask
      return $ if i == n then adjust n repl 
               else Var (if i > n then i - 1 else i) expl
  goVal x = return x

-- | Add @k@ to index of each open variable in @x@.
--
adjust :: Int -> GenericT
adjust k x = runIdentity $ runReaderT (walk (mkM goTm) x) 0 where
  goTm (Var i expl) = do
      n <- ask
      return $ Var (if i >= n then i + k else i) expl
  goTm x = return x


-- | Basic view without explanations.
--
data BasicValue = VarBV Nat 
		| AppBV Value Value 
		| LamBV Type (Abs Value)
		| LitBV Literal 
		| DefBV QName 
		| MetaVBV MId
  deriving (Typeable, Data)

data BasicType = ElBT Value Sort
	       | PiBT Type (Abs Type)
	       | SortBT Sort
	       | MetaTBT MId
  deriving (Typeable, Data)

data BasicSort = TypeBS Nat
	       | PropBS 
	       | MetaSBS MId
	       | LubBS Sort Sort
  deriving (Typeable, Data, Show)

basicValue :: Value -> BasicValue
basicValue v = case v of
    Var i _ -> VarBV i
    App v1 v2 _ _ -> AppBV v1 v2
    Lam a v _ -> LamBV a v
    Lit l _ -> LitBV l
    Def f _ -> DefBV f
    MetaV x _ -> MetaVBV x

basicType :: Type -> BasicType
basicType a = case a of
    El v s _ -> ElBT v s
    Pi a b _ -> PiBT a b
    Sort s _ -> SortBT s
    MetaT x _ -> MetaTBT x
				  
basicSort :: Sort -> BasicSort
basicSort s = case s of
    Type n _ -> TypeBS n
    Prop _ -> PropBS
    MetaS x _ -> MetaSBS x
    Lub s1 s2 _ -> LubBS s1 s2


-- | View as a spine, where head is always visible. 
--
data SpineValue = VarSV Nat [Value]
		| LamSV Type (Abs Value) [Value]
		| LitSV Literal -- ^ literals can't be applied
		| DefSV QName [Value]
		| MetaVSV MId [Value]
  deriving (Typeable, Data, Show)

spineValue :: Value -> SpineValue
spineValue v = app [] $ basicValue v where
    app args v = case v of
        VarBV i -> VarSV i args
	AppBV v1 v2 -> app (v2 : args) (basicValue v1)
	LamBV a v -> LamSV a v args
	LitBV l -> case args of [] -> LitSV l
	DefBV f -> DefSV f args
	MetaVBV x -> MetaVSV x args


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
  metaSt :: Store,
  cnstrSt :: Constraints,
  sigSt :: Signature
}

type TCErrMon = Either String

type TCM a = StateT TCState (ReaderT Context TCErrMon) a

-- | get globally new symbol (@Int@)
genSym = do
  v <- gets genSymSt
  modify (\st -> st{ genSymSt = v + 1})
  return v

--
-- Constraints
--
type ConstraintId = Int

data Constraint = ValueEq Type Value Value
		| TypeEq Type Type

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
                    UnderScoreV cIds -> UnderScoreV $ cId : cIds
                    UnderScoreT cIds -> UnderScoreT $ cId : cIds
                    UnderScoreS cIds -> UnderScoreS $ cId : cIds
                    HoleV sig ctx a cIds -> HoleV sig ctx a $ cId : cIds
                    HoleT sig ctx s cIds -> HoleT sig ctx s $ cId : cIds
                else mi
      in (id, mi')

--
-- Meta Variables
--
type MId = Int

data MetaInfo = InstV Value
	      | InstT Type
              | InstS Sort
	      | UnderScoreV [ConstraintId]
	      | UnderScoreT [ConstraintId]
	      | UnderScoreS [ConstraintId]
	      | HoleV Signature Context Type [ConstraintId]
	      | HoleT Signature Context Sort [ConstraintId]

type Store = [(MId, MetaInfo)]

-- | instantiate a type 
--   results is open meta variable or a non meta variable type.
instType :: Type -> TCM Type
instType a = case basicType a of
    (MetaTBT x) -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstT a') -> instType a'
            Just _ -> return a
    _ -> return a

-- | instantiate a sort 
--   results is open meta variable or a non meta variable sort.
instSort :: Sort -> TCM Sort
instSort s = case basicSort s of
    (MetaSBS x) -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstS s') -> instSort s'
            Just _ -> return s
    _ -> return s

--
-- Context & Signature
--
type Context = [CtxElm]
type Signature = Context

data CtxElm = Decl Name Type (Maybe [Name]) -- ^ ind. types have list of constructors
	    | Defn Name [Clause]
	    | NameSpace Name Context
  deriving (Typeable, Data, Show)

isDecl ce = case ce of Decl _ _ _ -> True; _ -> False
isDefn ce = case ce of Defn _ _ -> True; _ -> False
isNmsp ce = case ce of NameSpace _ _ -> True; _ -> False

-- | add a declaration to the context
addCtx :: Name -> Type -> TCM a -> TCM a
addCtx x a v = local ((Decl x a Nothing :) . adjust 1) v
    

-- | get type of bound variable (i.e. deBruijn index)
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

getConstInfo :: (Signature -> Name -> a) -> Signature -> QName -> a
getConstInfo fun ctx (Qual pkg name) = 
    case L.find (\ (NameSpace x _) -> x == pkg) (filter isNmsp ctx) of
        Just (NameSpace _ ctx') -> getConstInfo fun ctx' name
getConstInfo fun ctx (QName c) = fun ctx c

-- | get type of a constant 
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
--   Result of @reduce@ is whnf where arguments have already been reduced
--     i.e. @reduce (c m_1 m_2) ==> c v_1 v_2@ if @c@ is an undefined
--     constant and @reduce m_i ==> v_i@.
--
reduce store ctx sig v = go v where
    go v = case spineValue v of
        LamSV a (Abs _ v') (arg:args) -> go $ addArgs (subst (go arg) v') args
        MetaVSV x args -> case lookup x store of
            Just (InstV v) -> go $ addArgs v args 
            Just _ -> v
        DefSV f args -> case defOfConst f of
            [] -> v -- ^ no definition for head
            cls@(Clause ps _ : _) -> 
                if length ps == length args then appDef v cls args
                else if length ps > length args then
                    let (args1,args2) = splitAt (length ps) args 
                    in go $ addArgs (appDef v cls args1) args2
                else v -- ^ partial application
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
        goCls [] _ = v -- ^ no clause matched, can happen with parameter arguments
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
    ctx <- ask
    sig <- gets sigSt
    return $ reduce store ctx sig v


-- | View as a reduced spine, where head is always visible.
--   If head is a meta variable, then that variable is open.
--
data WhnfValue = VarWV Nat [Value]
                | LamWV Type (Abs Value)
                | LitWV Literal -- ^ literals can't be applied
                | DefWV QName [Value]
                | MetaVWV MId [Value] -- ^ MId shouldn't be instantiated
  deriving (Typeable, Data, Show)

whnfValue :: Value -> TCM WhnfValue
whnfValue v = do 
    v' <- reduceM v
    return $ case spineValue v' of
        VarSV i args -> VarWV i args
        LitSV c -> LitWV c
        LamSV a v [] -> LamWV a v
        DefSV f args -> DefWV f args
        MetaVSV x args -> MetaVWV x args


-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--
checkArgs args = go [] args where
    go _ [] = return ()
    go done (arg : args) = case basicValue arg of 
        VarBV i | not $ elem i done -> go (i:done) args
        _ -> fail "checkArgs"

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
findIdx p vs = go 0 vs where
    go i (v : vs) | p v = return i
    go i (_ : vs) = go (i + 1) vs
    go _ [] = fail "findIdx"


-- | Extended occurs check
--   Assumes value to be checked already in whnf
occ :: MId -> [Value] -> GenericM TCM
occ y okVars v = runReaderT (go v) 0 where
    go = walk (mkM occVal) -- `extM` occTyp
    occVal v = case spineValue v of
        VarSV i args -> do
            j <- findIdx undefined {- should be (v==) -}
			 okVars
            
            return $ var j

{-
-- | Assign a value to an open metavar.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given value.
--
assign :: MId  -> [Value] -> Value -> TCM ()
assign x args v = do
    checkArgs args
    v' <- occ x args v    
-}

-- | Type directed equality on values.
--
equalVal :: Type -> Value -> Value -> TCM ()
equalVal a m n = do
    a' <- instType a
    case basicType a' of
        PiBT a (Abs name b) -> 
            let p = Var 0 Duh
                m' = adjust 1 m
                n' = adjust 1 n
            in addCtx name a $ equalVal b (app m' p) (app n' p)
        MetaTBT x -> addCnstr [x] (ValueEq a m n) 
        _ -> equalAtm m n

-- | Syntax directed equality on atomic values
--
equalAtm :: Value -> Value -> TCM ()
equalAtm m n = do
    m' <- whnfValue m
    n' <- whnfValue n
    case (m', n') of
        (LitWV l1, LitWV l2) | l1 == l2 -> return ()
        (VarWV i iArgs, VarWV j jArgs) | i == j -> do
            a <- typeOfBV i
            equalArg a iArgs jArgs
        (DefWV x xArgs, DefWV y yArgs) | x == y -> do
            a <- typeOfConst x
            equalArg a xArgs yArgs
--        (MetaVWV x xArgs, n') -> assign x xArgs n'
        _ -> fail $ "equalAtm "++(show m)++" "++(show n)

-- | Type-directed equality on argument lists
--
equalArg :: Type -> [Value] -> [Value] -> TCM ()
equalArg a args1 args2 = do
    a' <- instType a
    case (basicType a', args1, args2) of 
        (_, [], []) -> return ()
        (PiBT b (Abs _ c), (arg1 : args1), (arg2 : args2)) -> do
            equalVal b arg1 arg2
            equalArg (subst arg1 c) args1 args2
        _ -> fail $ "equalArg "++(show a)++" "++(show args1)++" "++(show args2)

{-
data WhnfValue = VarWV Nat [Value]
                | LamWV Type (Abs Value)
                | LitWV Literal -- ^ literals can't be applied
                | DefWV QName [Value]
                | MetaVWV MId [Value] -- ^ MId shouldn't be instantiated

data BasicType = ElBT Value Sort
	       | PiBT Type (Abs Type)
	       | SortBT Sort
	       | MetaTBT MId
-}

---------------------------------------------------------------------------
--
-- Example
--

testRed v = runReaderT (evalStateT (reduceM v) testSt) []

testSt = TCSt {
  genSymSt = 0,
  metaSt = [],
  cnstrSt = [],
  sigSt = testSig
 }

testSig = [ -- probably wrong way to handle a datatype, but enough for now...

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


