{-# OPTIONS -fglasgow-exts #-}

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

import Debug.Trace

import qualified Data.List as L
import Data.Generics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

import Syntax.Common
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

addArgs = foldl (\x y -> App x y NotHidden Duh)

data Type = El Value Sort Expl
	  | Pi Type (Abs Type) Expl
	  | Sort Sort Expl
	  | MetaT MId Expl
  deriving (Typeable, Data, Show)

data Sort = Type Nat Expl
	  | Prop Expl
	  | MetaS MId Expl 
	  | Lub Sort Sort Expl
  deriving (Typeable, Data, Show)

data Abs a = Abs Name a deriving (Typeable, Data, Show)

-- | check if given term is an abstraction
isAbs x = dataTypeName (dataTypeOf x) == dataTypeName (dataTypeOf (Abs (Name noRange "") ()))

-- | apply @f@ everywhere in a term, 
--   Local reader state keeps track of how many binders have been passed.
--   Might want to add some way to not traverse explanations.
walk :: Monad m => GenericM (ReaderT Int m) -> GenericM (ReaderT Int m)
walk f x = do
    x' <- f x
    if isAbs x then local (+ 1) $ gmapM (walk f) x' else gmapM (walk f) x'

-- | substitute @repl@ for @(Var 0 _)@ in @x@
subst repl x = runIdentity $ runReaderT (walk (mkM goTm) x) 0 where
  goTm (Var i expl) = do
      n <- ask
      return $ if i == n then adjust n repl 
               else Var (if i > n then i - 1 else i) expl
  goTm x = return x

-- | add @k@ to index of each open variable in @x@
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
-- Constraints
--
type ConstraintId = Int

data Constraint = ValueEq Type Value Value
		| TypeEq Type Type

type Constraints = [(ConstraintId,(Signature,Context,Constraint))]


--
-- Meta Variables
--
type MId = Int

data MetaInfo = InstV Value
	      | InstT Type
	      | UnderScoreV [ConstraintId]
	      | UnderScoreT [ConstraintId]
	      | HoleV Signature Context Type [ConstraintId]
	      | HoleT Signature Context Type [ConstraintId]

type Store = [(MId, MetaInfo)]


--
-- Monad
--
data TCState = TCSt {
  genSym :: Int,
  metaSt :: Store,
  cnstrSt :: Constraints,
  sigSt :: Signature
}

type TCErrMon = Either String

type TCM a = StateT TCState (ReaderT Context TCErrMon) a

--
-- Context & Signature
--
type Context = [CtxElm]
type Signature = Context

data CtxElm = Decl Name Type
	    | Defn Name [Clause]
	    | NameSpace Name Context
  deriving (Typeable, Data, Show)

isDecl ce = case ce of Decl _ _ -> True; _ -> False
isDefn ce = case ce of Defn _ _ -> True; _ -> False
isNmsp ce = case ce of NameSpace _ _ -> True; _ -> False

-- | get type of bound variable (i.e. deBruijn index)
typeOfBV :: Nat -> TCM Type
typeOfBV n = do
    ctx <- ask
    case (filter isDecl ctx) !! n of
        Decl _ a -> return a

-- | get either type or definition of a constant. 
--   this navigates namespace structure and uses passed
--     function to find data after right namespace is reached
--
getConstInfo :: (Signature -> Name -> TCM a) -> QName -> TCM a
getConstInfo fun c = do
    ctx <- ask  -- ^ need to look here for local definitions
    sig <- gets sigSt 
    go (ctx++sig) c
  where
    go ctx (Qual pkg name) = 
        case L.find (\ (NameSpace x _) -> x == pkg) (filter isNmsp ctx) of
            Just (NameSpace _ ctx) -> go ctx name
    go ctx (QName c) = fun ctx c

-- | get type of a constant 
typeOfConst :: QName -> TCM Type
typeOfConst = getConstInfo find where
    find sig c = case L.find (\ (Decl x _) -> x == c) (filter isDecl sig) of
        Just (Decl _ a) -> return a

-- | get definition of a constant (i.e. a list of clauses)
defOfConst :: QName -> TCM [Clause]
defOfConst = getConstInfo find where
    find sig c = case L.find (\ (Defn x _) -> x == c) (filter isDefn sig) of
        Just (Defn _ cls) -> return cls


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

-- | match the given patterns to the given arguments.
--   returns updated list of values to instantiate the 
--     bound variables in the patterns.
--
matchPats :: [Value] -> [Pattern] -> [Value] -> TCM [Value]
matchPats curArgs (pat:pats) (arg:args) = do
    newArgs <- matchPat curArgs pat arg
    matchPats newArgs pats args
matchPats curArgs [] [] = return curArgs

matchPat :: [Value] -> Pattern -> Value -> TCM [Value]
matchPat curArgs WildP _ = return curArgs
matchPat curArgs (VarP x) arg = return $ curArgs++[arg]
matchPat curArgs (ConP c pats) arg = do
    v <- reduce arg
    case spineValue v of
        DefSV c' args | c' == c -> matchPats curArgs pats args
        _ -> fail "pattern mismatch"


--
-- Reduction
--

-- | reduce a value to head-normal form
reduce :: Value -> TCM Value
reduce v = case spineValue v of
    LamSV a (Abs _ v') (arg:args) -> reduce $ subst arg v'
    MetaVSV x args -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstV v) -> reduce $ addArgs v args 
  	    Just _ -> return v
    DefSV f args -> do
        def <- defOfConst f
        case def of
            [] -> return v -- no definition for head
            cls@(Clause ps _ : _) -> 
                if length ps == length args then appDef f cls args
                else return v
    _ -> return v

-- | apply a defined function to it's arguments
--   first arg is function name and is passed for error reporting
--
appDef :: QName -> [Clause] -> [Value] -> TCM Value
appDef f cls args = goCls cls args where
    -- | type checker should guarantee that we can't get a pattern match exception
    --     so only one case for goCls is needed
    goCls (cl@(Clause pats body) : cls) args =
        catchError (do args' <- matchPats [] pats args 
		       app args' body
                   )
                   (\ _ -> goCls cls args)
    app [] (Body v) = return v
    app (arg : args) (Bind (Abs _ body)) = app args $ subst arg body
	

---------------------------------------------------------------------------
--
-- Example
--

testRed v = runReaderT (evalStateT (reduce v) testSt) []

testSt = TCSt {
  genSym = 0,
  metaSt = [],
  cnstrSt = [],
  sigSt = testSig
 }

testSig = [ -- probably wrong way to handle a datatype, but enough for now...

  -- nat : set_0
  Decl (Name noRange "nat") (Sort (Type 0 Duh) Duh),

  -- Z : nat
  Decl (Name noRange "Z") (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh),
  Defn (Name noRange "Z") [],

  -- S : nat -> nat
  Decl (Name noRange "S") (
    Pi (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) 
       (Abs (Name noRange "_") $ El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) 
       Duh 
  ),
  Defn (Name noRange "S") [],

  -- plus : nat -> nat -> nat
  Decl (Name noRange "plus") (
    Pi (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) (Abs (Name noRange "_") $
    Pi (El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) (Abs (Name noRange "_") $
    El (Def (QName $ Name noRange "nat") Duh) (Type 0 Duh) Duh) Duh) Duh 
  ),

  Defn (Name noRange "plus") [ 

    -- plus Z n = n
    Clause [ConP (QName $ Name noRange "Z") [], VarP $ Name noRange "n"] $ Body $ Var 0 Duh,

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

app x y = App x y NotHidden Duh
s = Def (QName $ Name noRange "S") Duh
z = Def (QName $ Name noRange "Z") Duh
plus = Def (QName $ Name noRange "plus") Duh

two = app s (app s z)
three = app s (app s (app s z))


