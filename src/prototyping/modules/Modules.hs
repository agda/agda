
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

data Def = NoDef | YesDef Term
  deriving Show

lookUp m x = y
  where
    Just y = Map.lookup x m

(f -*- g) (x,y) = (f x,g y)
infixl 8 <$>, <*>
f <$> m = liftM f m
f <*> x = ap f x

m1 `isSubModuleOf` m2 = m2 `isPrefixOf` m1

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
class Apply t where
  apply :: t -> [Term] -> t

instance Apply Term where
  apply t []	       = t
  apply (Var n ts) us  = Var n $ ts ++ us
  apply (Def x ts) us  = Def x $ ts ++ us
  apply (Lam t) (u:us) = subst u t `apply` us

instance Apply Def where
  apply NoDef _	      = NoDef
  apply (YesDef t) us = YesDef $ t `apply` us

-- Abstraction. The telescope should be free in the term.
class Abstract t where
  abstract :: Tel -> t -> t

instance Abstract Term where
  abstract [] t	   = t
  abstract (_:tel) t = Lam $ abstract tel t

instance Abstract Def where
  abstract tel NoDef	  = NoDef
  abstract tel (YesDef t) = YesDef $ abstract tel t

-- Raising the level of a term.
class Raise t where
  raiseByFrom :: Int -> Int -> t -> t

instance Raise Term where
  raiseByFrom k n (Lam t)    = Lam $ raiseByFrom k (n + 1) t
  raiseByFrom k n (Def x ts) = Def x $ raiseByFrom k n ts
  raiseByFrom k n (Var m ts) = Var (raise m) $ raiseByFrom k n ts
    where
      raise m | m >= n	= m + k
	      | otherwise	= m

instance Raise Def where
  raiseByFrom k n NoDef	     = NoDef
  raiseByFrom k n (YesDef t) = YesDef $ raiseByFrom k n t

instance Raise t => Raise [t] where
  raiseByFrom k n ts = List.map (raiseByFrom k n) ts

raiseBy n = raiseByFrom n 0
raise t	  = raiseBy 1 t

-- Substituting a term for a free variable in something.
class Subst t where
  substFor :: Int -> Term -> t -> t

subst u = substFor 0 u

instance Subst Term where
  substFor n u (Lam t)    = Lam $ substFor (n + 1) (raise u) t
  substFor n u (Def x ts) = Def x $ substFor n u ts
  substFor n u (Var m ts) = sub m `apply` substFor n u ts
    where
      sub m | m < n  = Var m []
	    | m > n  = Var (m - 1) []
	    | m == n = u

instance Subst Def where
  substFor n u NoDef      = NoDef
  substFor n u (YesDef t) = YesDef $ substFor n u t

instance Subst t => Subst [t] where
  substFor n u ts = List.map (substFor n u) ts

{-
  Now the lookup functions. First we should think about what results we want to
  get.  There are really two problems: first, to look up a definition with all
  the right free variables, and second, to instantiate these free variables to
  the proper things from the context. Let's solve only the first problem to
  begin with. For this, the current context is irrelevant so we can look at the
  problem globally.

  When using a flat structure there is a problem when you want to access
  submodules to an implicitly defined module. For instance T.E.D from the
  example below.

  There are a few possible solutions:

    (1) Add all submodules to the signature. This would make lookup very simple
	but would some work at typechecking (going through the signature
	looking for submodules of the instantiated module).

    (2) Look for parent modules if a module isn't found. Doesn't require any
	work at typechecking, but on the other hand lookup gets complicated
	(and inefficient).

  Conclusion: go with curtain number (1).

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
    Impl tel m' args  -> instMDef tel args $ lookupModule0 sig m'
    d		      -> d

-- instMDef Γ us (Expl Δ f) = Expl Γ (λ Γ. f us), where Γ ⊢ us : Δ
instMDef :: Tel -> Args -> MDef -> MDef
instMDef tel us (Expl tel' f) = Expl tel (Map.map inst f)
  where
    inst t = abstract tel $ t `apply` us

{-

  Now to tackle the second problem. Above the returned definition is valid in
  the empty context. All the free variables have been abstracted over. There
  are two cases to consider:

    (1) Looking up the type of a function (during type checking)

	- When type checking we need to know the number of free variables to do
	  the translation to the lifted version.
	- This we can get from the telescope of the module returned by
	  lookupModule.
	- Question: what is the relationship between this telescope and the
	  current context?

	    module T (x:A) where
	      module A (y:B) where
		f = e
	      module B = A t  -- module B (x:A) = A x t
	      g xs = B.f

	- Answer: since we can only refer to things from fully instantiated
	  modules the telescope of the module is a prefix of the current
	  context.

    (2) Looking up the definition of a function (during reduction)

	Here we are happy to get the lifted definition, since we assume that
	all uses of the function has been translated to an application of the
	lifted version. In other words, for this lookupName0 works fine.

  So do we need two different functions? The way it's solved in agdaLight is to
  return the type of the original thing, and the definition of the lifted
  thing.

-}

-- Returns a closed definition (and the variables abstracted over).
lookupName :: Sig -> QName -> (Tel, Def)
lookupName sig (m,x) = (tel, lookUp f x)
  where
    Expl tel f = lookupModule sig m

lookupDef :: Sig -> QName -> Def
lookupDef sig q = snd $ lookupName sig q

-- Instantiate a closed definition in the current context. Precondition:
-- the context of the definition is a prefix of the current context (first
-- argument).
instantiateDef :: Tel -> (Tel, Def) -> Def
instantiateDef ctx (tel,d) = d `apply` vs
  where
    -- ctx = ΓΔ, tel = Γ, d = λ Γ. e
    -- ΓΔ ⊢ vs : Γ
    -- so ΓΔ ⊢ d vs
    n  = length tel
    k  = length ctx - n
    vs = reverse [ Var (i + k) [] | i <- [0..n - 1] ]

-- Always Expl
lookupModule :: Sig -> MName -> MDef
lookupModule = lookupModule0


-- Reduction. All function applications have been translated to lifted versions.
class Reduce t where
  reduce :: Sig -> t -> t

instance Reduce Term where
  reduce sig (Def x vs) =
    case lookupDef sig x of
      NoDef     -> Def x $ reduce sig vs
      YesDef t  -> reduce sig $ t `apply` vs
  reduce sig (Var x vs) = Var x $ reduce sig vs
  reduce sig (Lam t)	= Lam t

instance Reduce Def where
  reduce sig NoDef	= NoDef
  reduce sig (YesDef t) = YesDef $ reduce sig t

instance Reduce t => Reduce [t] where
  reduce sig ts = List.map (reduce sig) ts

{-

  We moved a lot of work to the building of the signature. Here's how that's
  supposed to work:

  Things to take care of:

  - Module names are unqualified.

  - Telescopes (arguments) only cover the parameters to the defined
    (instantiated) module and not the parameters of the parents.

  - Submodules of instantiated modules need to be added to the signature. To do
    this we have to go through the signature so far and duplicate modules.

  - Uses of a function must be translated to a use of the lifted version of the
    function.

-}

data Decl = ModImpl Name Tel MName [Expr]
	  | ModExpl Name Tel [Decl]
	  | Defn Name Expr
	  | Const Name
  deriving Show

data Expr = EVar Name
	  | EDef QName
	  | EApp [Expr]
	  | ELam Name Expr
  deriving Show

type Context = Tel -- only backwards
type TCM = ReaderT (MName,Context) (State Sig)

-- Type checking monad utilities

currentModule :: TCM MName
currentModule = asks fst

withCurrentModule :: MName -> TCM a -> TCM a
withCurrentModule m = local $ const m -*- id

getContext :: TCM Tel
getContext = asks snd

getSignature :: TCM Sig
getSignature = get

extendContext :: Name -> TCM a -> TCM a
extendContext x = local $ id -*- (x:)

extendContextWithTel :: Tel -> TCM a -> TCM a
extendContextWithTel tel = foldr (.) id $ List.map extendContext tel

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

addModule :: MName -> MDef -> TCM ()
addModule m md = modify $ Map.insert m md

forEachModule :: (MName -> Bool) -> (MName -> TCM a) -> TCM [a]
forEachModule p go =
  do  sig <- getSignature
      concat <$> mapM action (Map.keys sig)
  where
    action m
      | p m	  = (:[]) <$> go m
      | otherwise = return []

forEachModule_ :: (MName -> Bool) -> (MName -> TCM a) -> TCM ()
forEachModule_ p go = forEachModule p go >> return ()

-- Running the type checker

typeCheck :: Decl -> Sig
typeCheck d = runTCM $ checkDecl d >> getSignature

runTCM :: TCM a -> a
runTCM m = flip evalState Map.empty
	   $ flip runReaderT ([],[]) m

-- Type checking

checkDecl :: Decl -> TCM ()

checkDecl (Const x) =
  do  q <- qualify x
      addDef q NoDef

checkDecl (Defn x e) =
  do  q <- qualify x
      addDef q NoDef  -- definitions can be recursive
      t <- checkExpr e
      gamma <- reverse <$> getContext
      addDef q (YesDef $ abstract gamma t)

{-
  If M' is qualified we know that its parent is fully instantiated. In other
  words M' is a valid module in a prefix of the current context.

  Current context: ΓΔ

  Without bothering about submodules of M':
    Γ   ⊢ module M' Ω
    ΓΔ  ⊢ module M Θ = M' us
    ΓΔΘ ⊢ us : Ω

    Expl ΓΩ _ = lookupModule M'
    addModule M ΓΔΘ = M' Γ us

  Submodules of M':

    Forall submodules A
      ΓΩΦ ⊢ module M'.A Ψ ...

    addModule M.A ΓΔΘΦΨ = M'.A Γ us ΦΨ

-}
checkDecl (ModImpl x theta m' args) =
  do  sig	 <- getSignature
      m		 <- qualifyModule x
      gammaDelta <- reverse <$> getContext
      let Expl gammaOmega f = lookupModule sig m'
	  (gamma,omega)	    = splitAt (length gammaOmega - length args) gammaOmega
	  delta		    = drop (length gamma) gammaDelta
	  vs0		    =
	    reverse [ Var (i + length delta + length theta) []
		    | i <- [0..length gamma - 1]
		    ]
      vs  <- extendContextWithTel theta
	      $ mapM checkExpr args -- should check against Ω
      addModule m $ Impl (gammaDelta ++ theta) m' (vs0 ++ vs)
      forEachModule_ (\m'a -> m'a `isSubModuleOf` m') $ \m'a ->
	do  let Expl gammaOmegaPhiPsi _ = lookupModule sig m'a
		ma	= m ++ drop (length m') m'a
		phiPsi	= drop (length gammaOmega) gammaOmegaPhiPsi
		vs1	= reverse [ Var i [] | i <- [0..length phiPsi - 1] ]
	    addModule ma $ Impl (gammaDelta ++ theta ++ phiPsi)
				m'a
				(vs0 ++ vs ++ vs1)

checkDecl (ModExpl x tel ds)	 =
  do  m <- qualifyModule x
      withCurrentModule m
	$ extendContextWithTel tel
	$ do  tel' <- reverse <$> getContext
	      addModule m $ Expl tel' Map.empty
	      mapM_ checkDecl ds

checkExpr :: Expr -> TCM Term

checkExpr (ELam x e) =
  extendContext x $ Lam <$> checkExpr e

checkExpr (EDef x)      =
  do  sig	 <- getSignature
      gammaDelta <- reverse <$> getContext
      let (gamma, _) = lookupName sig x
	  k	     = length gammaDelta - length gamma
	  vs	     = reverse $ [ Var (i + k) [] | i <- [0..length gamma - 1] ]
      return $ Def x vs

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
  module T t1 t2 where
    const c
    module A a where
      f = \x -> a x t1 t2
      g = f c
    module B b1 b2 b3 = A (t1 t2 b1 b2 b3)
    module B' = B t2 t1 c
    module C c where
      module D = B (t2 c) (c t2) t1
    module E = C (t2 t2 t1)

-}
prog :: Decl
prog =
  ModExpl "T" ["t1","t2"]
  [ Const "c"
  , ModExpl "A" ["a"]
    [ Defn "f" $ ELam "x" $ EApp [EVar "a", EVar "x", EVar "t1", EVar "t2"]
    , Defn "g" $ EApp [eDef "T.A.f", eDef "T.c"]
    ]
  , ModImpl "B" ["b1","b2","b3"] ["T","A"] [EApp $ List.map EVar $ words "t1 t2 b1 b2 b3"]
  , ModImpl "B'" [] ["T","B"] [EVar "t2", EVar "t1", eDef "T.c"]
  , ModExpl "C" ["c"]
    [ ModImpl "D" [] ["T","B"] [EApp [EVar "t2",EVar "c"], EApp [eDef "T.c", EVar "t2"], EVar "t1"]
    ]
  , ModImpl "E" [] ["T","C"] [EApp $ List.map EVar $ words "t2 t2 t1"]
  ]

sig = typeCheck prog

eDef s = EDef (qname s)
qname s = case reverse $ words $ List.map undot s of
	    x:xs  -> (reverse xs,x)
  where
    undot '.' = ' '
    undot  x  =  x

test :: Tel -> Expr -> String
test tel e =
  runTCM $
  do  put sig
      t <- extendContextWithTel tel $ checkExpr e
      return $ showT tel $ reduce sig t

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
