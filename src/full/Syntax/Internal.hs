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

import qualified Data.List as L
import Data.Generics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader

-- | @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
data Value = Var Nat Expl
	   | App Value Value Hidden Expl
	   | Lam Type (Abs Value) Expl
	   | Lit Literal Expl
	   | Def NamePath Expl 
	   | MetaV MId Expl
  deriving (Typeable, Data, Show)

addArgs = foldl (\x y -> App x y False Duh)

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
isAbs x = dataTypeName (dataTypeOf x) == dataTypeName (dataTypeOf (Abs "" ()))

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

-- | Explanations should contain enough information to 
--   reconstruct a derivation
data Expl = InCode Range
	  | DefinedAt Range
	  | Expl :+: Expl
	  | Duh -- ^ this is a default for development which should disappear
  deriving (Typeable, Data, Show)

-- | Basic view without explanations.
data BasicValue = VarBV Nat 
		| AppBV Value Value 
		| LamBV Type (Abs Value)
		| LitBV Literal 
		| DefBV NamePath 
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

-- | View as a spine, where head is always visible. ----------------
data SpineValue = VarSV Nat [Value]
		| LamSV Type (Abs Value) [Value]
		| LitSV Literal -- ^ literals can't be applied
		| DefSV NamePath [Value]
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
-- Stuff to be put in other files later
--
--------------------------------------------------------------
type Nat = Int
type MId = Int
newtype Range = Range (Int, Int) deriving (Typeable, Data, Show)
type Hidden = Bool
type Name = String
type NameSpace = String
-- | @NamePath@ is a list of namespaces, with their arguments, 
--     and the name of the constant
type NamePath = ([(NameSpace,[Value])],Name)
data Literal = String String | Int Int deriving (Typeable, Data, Show)

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
data MetaInfo = InstV Value
	      | InstT Type
	      | UnderScoreV [ConstraintId]
	      | UnderScoreT [ConstraintId]
	      | HoleV Signature Context Type [ConstraintId]
	      | HoleT Signature Context Type [ConstraintId]

type Store = [(MId, MetaInfo)]

--
-- Context & Signature
--
type Context = [CtxElm]
type Signature = Context

data CtxElm = Decl Name Type
	    | Defn Name [Clause]
	    | NameSpace Name Context
  deriving (Typeable, Data)

isDecl ce = case ce of Decl _ _ -> True; _ -> False
isDefn ce = case ce of Defn _ _ -> True; _ -> False

-- | get type of bound variable (i.e. deBruijn index)
typeOfBV :: Nat -> TCM Type
typeOfBV n = do
  ctx <- ask
  case (filter isDecl ctx) !! n of
    Decl _ a -> return a

-- | get type of a constant 
typeOfConst :: Name -> TCM Type
typeOfConst c = do
  ctx <- gets sigSt 
  case L.find (\ (Decl x _) -> x == c) (filter isDecl ctx) of
    Just (Decl _ a) -> return a

-- | get definition of a constant (i.e. a list of clauses)
defOfConst :: Name -> TCM [Clause]
defOfConst c = do
  ctx <- ask  -- need to look in context for local definitions
  sig <- gets sigSt
  case L.find (\ (Defn x _) -> x == c) (filter isDefn $ ctx++sig) of
    Just (Defn _ cls) -> return cls

--
-- Definitions
--
data Clause = Clause [Pattern] Value
  deriving (Typeable, Data) 

data Pattern = VarP Name
	     | ConP Name [Pattern]
	     | PairP Pattern Pattern
             | WildP
  deriving (Typeable, Data)

-- | reduce a value to head-normal form
reduce v = case spineValue v of
    LamSV a (Abs _ v') (arg:args) -> reduce $ subst arg v'
    MetaVSV x args -> do 
        store <- gets metaSt
        case lookup x store of
            Just (InstV v) -> reduce $ addArgs v args 
  	    Just _ -> return v
    DefSV f args -> case defOfConst f of
        [] -> return v -- no definition for head
        cls@(Clause ps v : _) -> 
            if length ps == length args then appDef f cls args
            else return v
    _ -> return v

{-
appDef f cls [] = return $ 
appDef _ [] args = fail "pattern match exception"
appDef f (Clause p v : cls) (arg : args) = 
-}

--
-- Monad
--
data TCState = TCSt {
  genSym :: Int,
  metaSt :: Store,
  cnstrSt :: Constraints,
  sigSt :: Signature
}

type TCM a = StateT TCState (Reader Context) a

