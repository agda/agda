
import Control.Monad.State
import Control.Monad.Reader
import Data.List as List
import Data.Map as Map

{-

  Simplified module system, to illustrate how it works.

-}

type Name  = String
type MName = [Name]
type QName = (MName, Name)

type Sig = Map MName MDef

type Var  = Int	    -- deBruijn variables
data Term = Def QName [Term]
	  | Var Var [Term]
	  | Lam Term
  deriving Show
type Tel  = [Name]  -- we don't care about types
type Args = [Term]

{-
  Telescopes bind all free variables in the module (and consequently
  arguments in implicit modules define all free variables.
-}
data MDef = Impl Tel MName Args
	  | Expl Tel (Map Name Def)
  deriving Show

type Def = Term

lookUp m x = y
  where
    Just y = Map.lookup x m

(f -*- g) (x,y) = (f x,g y)
infixl 8 <$>, <*>
f <$> m = liftM f m
f <*> x = ap f x

-- Simple version (ignoring free variables) -------------------------------

lookupName_ :: Sig -> QName -> Def
lookupName_ sig (m,x) = lookUp f x
  where
    Expl _ f = lookupModule_ sig m

-- Always Expl
lookupModule_ :: Sig -> MName -> MDef
lookupModule_ sig m =
  case lookUp sig m of
    Impl _ m' _	-> lookupModule_ sig m'
    d		-> d

-- Taking free variables into account -------------------------------------

-- First some helpers

-- Application
apply :: Term -> [Term] -> Term
apply (Var n ts) us  = Var n $ ts ++ us
apply (Def x ts) us  = Def x $ ts ++ us
apply (Lam t) (u:us) = subst [u] t `apply` us

-- Raising the level of a term.
raiseByFrom :: Int -> Int -> Term -> Term
raiseByFrom k n (Lam t)	   = Lam $ raiseByFrom k (n + 1) t
raiseByFrom k n (Def x ts) = Def x $ List.map (raiseByFrom k n) ts
raiseByFrom k n (Var m ts) = Var (raise m) $ List.map (raiseByFrom k n) ts
  where
    raise m | m >= n	= m + k
	    | otherwise	= m

raiseBy n = raiseByFrom n 0

-- Substituting a list of terms for the first free variables of a term.
subst :: [Term] -> Term -> Term
subst us (Lam t)    = Lam $ subst (Var 0 [] : List.map (raiseBy 1) us) t
subst us (Def x ts) = Def x $ List.map (subst us) ts
subst us (Var m ts) = sub m `apply` List.map (subst us) ts
  where
    sub m | m < length us = us !! m
	  | otherwise	  = Var (m - length us) []

{-
  Now the lookup functions. First we should think about what results we want to
  get.  There are really two problems: first, to look up a definition with all
  the right free variables, and second, to instantiate these free variables to
  the proper things from the context. Let's solve only the first problem to
  begin with. For this, the current context is irrelevant so we can look at the
  problem globally.

  When using a flat structure there is a problem when you want to access submodules
  to an implicitly defined module. For instance T.E.D from the example below.

  There are a few possible solutions:

    (1) Add all submodules to the signature. This would make lookup very simple
	but would some work at typechecking (going through the signature
	looking for submodules of the instantiated module).

    (2) Look for parent modules if a module isn't found. Doesn't require any work
	at typechecking, but on the other hand lookup gets complicated (and
	inefficient).

  Conclusion: go with curtain number (1).

  So the only difference from the very simple model above is that when
  following an implicit module definition we have to substitute the arguments.
  On the other hand we have ignored a fair amount of work that has to be done
  when adding modules to the signature.

-}

lookupName0 :: Sig -> QName -> Def
lookupName0 sig (m,x) = lookUp f x
  where
    Expl _ f = lookupModule0 sig m


-- Always Expl
lookupModule0 :: Sig -> MName -> MDef
lookupModule0 sig m =
  case lookUp sig m of
    Impl tel m' args  -> substMDef tel args $ lookupModule0 sig m'
    d		      -> d

-- substMDef Γ γ (Expl Δ f) = Expl Γ fγ, where γ : Γ -> Δ
substMDef :: Tel -> Args -> MDef -> MDef
substMDef tel args (Expl _ f) = Expl tel (Map.map (subst $ reverse args) f)

{-

  Now to tackle the second problem. Above the returned definition is valid in
  the context of the referring module (A.B.C.f returns the definition of f
  valid in the context inside A.B.C). When looking up a definition we want
  something valid in the current context.

  First observe that the only time we look up definitions from uninstantiated
  modules is when we are still inside these modules. This means that the
  definition we get will be valid in a subcontext to the current context, so we
  simply have to raise the definition by number of "new" variables.

  Note: this gets more complicated with local definitions.

-}

lookupName :: Tel -> Sig -> QName -> Def
lookupName ctx sig (m,x) = raiseBy (length ctx - length tel) (lookUp f x)
  where
    Expl tel f = lookupModule sig m

-- Always Expl
lookupModule :: Sig -> MName -> MDef
lookupModule = lookupModule0


{-

  We moved a lot of work to the building of the signature. Here's how that's
  supposed to work:

  Things to take care of:

  - Module names are unqualified.

  - Telescopes (arguments) only cover the parameters to the defined
    (instantiated) module and not the parameters of the parents.

  - Submodules of instantiated modules need to be added to the signature. To do
    this we have to go through the signature so far and duplicate modules.

  There is another problem that I didn't think of, namely when computing with
  things from parameterised modules (or local functions). To solve this problem
  the easiest thing to do is to build closures around functions with free
  variables.

  When computing with things from parameterised modules or local functions it's
  important that when you unfold you get something that's actually correct in
  the current context.

  To achieve this we should store the lifted definitions in the context
  (together with something saying how many free variables there are?). In
  agdaLight we don't lift the type.

  Example:

  module Top (y:N) where
    module A (x:N) where
      f = e[f,x,y]

    module B = A zero

  Top.A: f --> \y x -> e[Top.A.f y x, x, y]
  Top.B: f --> \y -> e[Top.A.f y zero, zero, y]

  How do we get Top.B.f? And how do we store it?

    Top.A (y:N)(x:N) --> f |-> \y x -> e[Top.A.f y x, x, y]
    Top.B (y:N)	     --> Top.A y zero

  Looking up Top.B.f:

	Top.B (y:N) --> Top.A y zero
    so	Top.B.f	    --> \y -> Top.A.f y zero

	Top.A.f	    --> \y x -> e[Top.A.f y x, x, y]
    and Top.B.f     --> \y -> e[Top.A.f y zero, zero, y]

  When typechecking a call to a definition we have to apply it to an
  appropriate prefix of the current context.


-}

data Decl = ModImpl Name Tel MName [Expr]
	  | ModExpl Name Tel [Decl]
	  | Defn Name Expr
  deriving Show

data Expr = EVar Name
	  | EDef QName
	  | EApp [Expr]
  deriving Show

type Context = Tel -- only backwards
type TCM = ReaderT (MName,Context) (State Sig)

-- Type checking monad utilities

currentModule :: TCM MName
currentModule = asks fst

getContext :: TCM Tel
getContext = asks snd

getSignature :: TCM Sig
getSignature = get

extendContext :: Name -> TCM a -> TCM a
extendContext x = local $ id -*- (x:)

qualify :: Name -> TCM QName
qualify x =
  do  m <- currentModule
      return (m,x)

qualifyModule :: Name -> TCM MName
qualifyModule x =
  do  m <- currentModule
      return $ m ++ [x]

addDef :: QName -> Def -> TCM ()
addDef (m,x) d = modify $ Map.adjust (\ (Expl tel f) -> Expl tel $ Map.insert x d f ) m

-- Running the type checker

typeCheck :: Decl -> Sig
typeCheck d = flip execState Map.empty
	    $ flip runReaderT ([],[])
	    $ checkDecl d

-- Type checking

checkDecl :: Decl -> TCM ()
checkDecl (Defn x e) =
  do  t <- checkExpr e
      q <- qualify x
      addDef q t
checkDecl (ModImpl x tel m args) = undefined
checkDecl (ModExpl x tel ds)	 = undefined

checkExpr :: Expr -> TCM Term
checkExpr (EDef x)      = return $ Def x []
checkExpr (EVar x)	= Var <$> checkVar x <*> return []
checkExpr (EApp (e:es)) =
  do  t <- checkExpr e
      ts <- mapM checkExpr es
      return $ t `apply` ts

checkVar :: Name -> TCM Var
checkVar x =
  do  ctx <- getContext
      case List.findIndex (x==) ctx of
	Just n	-> return n
	Nothing	-> fail $ "no such var: " ++ x

-- Example ----------------------------------------------------------------

{-
  module T Φ where
    module A Δ where
      f = e
    module B Γ = A us
    module B'  = B us'
    module C Θ where
      module D = B vs
    module E = C ws

  Concretely

  module T t1 t2 where
    module A a where
      f = a t2 t1
    module B b1 b2 b3 = A (t1 t2 b1 b2 b3)
    module B' = B t2 t1 t2
    module C c where
      module D = B (t2 t1) (t1 t2) c
    module E = C (t2 t2 t1)

-}
sig :: Sig
sig = Map.fromList
  [ ( ["T"]	    , Expl phi Map.empty			  )
  , ( ["T","A"]	    , Expl (phi ++ delta) (Map.singleton "f" e)	  )
  , ( ["T","B"]	    , Impl (phi ++ gamma) ["T","A"] us		  )
  , ( ["T","B'"]    , Impl phi ["T","B"] us'			  )
  , ( ["T","C"]	    , Expl (phi ++ theta) Map.empty		  )
  , ( ["T","C","D"] , Impl (phi ++ theta) ["T","B"] vs		  )
  , ( ["T","E"]	    , Impl phi ["T","C"] ws			  )
  , ( ["T","E","D"] , Impl phi ["T","B"] (List.map (subst $ reverse ws) vs) )
  ]
  where
    -- The two first term (corresponding to Φ) have to be added by the type checker.
    us	  = [var [4],var [3],var [4,3,2,1,0]]		  -- us  : ΦΓ -> ΦΔ
    us'	  = [var [1],var [0],var [0],var [1],var [0]]	  -- us' : Φ  -> ΦΓ
    vs	  = [var [2],var [1],var [1,2],var [2,1],var [0]] -- vs  : ΦΘ -> ΦΓ
    ws	  = [var [0],var [1],var [0,0,1]]		  -- ws  : Φ  -> ΦΘ

    e	  = var [0,1,2]     -- ΦΔ ⊢ e

    var (x:xs) = Var x $ List.map (var . (:[])) xs

phi   = ["t1","t2"]
delta = ["a"]
gamma = ["b1","b2","b3"]
theta = ["c"]

showT :: Tel -> Term -> String
showT ctx t =
  case t of
    Var n ts  -> (reverse ctx !! n) `app` ts
    Def x ts  -> showQ x `app` ts
  where
    showQ (m,x) = concat $ intersperse "." $ m ++ [x]
    app s [] = s
    app s ts = "(" ++ unwords (s : List.map (showT ctx) ts) ++ ")"

-- vim: sts=2 sw=2
