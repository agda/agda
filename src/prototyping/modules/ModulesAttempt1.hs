
{-

  Simplified module system, to illustrate how it works. Only it doesn't work
  like this... see bottom (before Example).

-}

type Name  = String
type MName = [Name]
type QName = (MName, Name)

type Sig = Name -> MDef

type Var  = Int	    -- deBruijn variables
type Term = [Var]
type Type = ()	    -- we don't care about types here
type Tel  = [Type]
type Args = [Term]

data MDef = Impl Tel MName Args
	  | Expl Tel (Name -> Def) (Name -> MDef)

type Def  = Term

-- Simple version (ignoring free variables) -------------------------------

lookupName_ :: Sig -> QName -> Def
lookupName_ sig (m,x) = names x
  where
    Expl _ names _ = lookupModule_ sig m

-- Always Expl
lookupModule_ :: Sig -> MName -> MDef
lookupModule_ sig (x:m) = look (sig x) m
  where
    look (Impl _ m' _) m       = lookupModule_ sig (m' ++ m)
    look (Expl _ _ mods) (x:m) = look (mods x) m
    look m []		       = m

-- Taking free variables into account -------------------------------------

-- First some helpers

-- Raising the level of a term.
raiseByFrom :: Int -> Int -> Term -> Term
raiseByFrom k n t = map raise t
  where
    raise m | m >= n	= m + k
	    | otherwise	= m

raiseBy n = raiseByFrom n 0

-- Substituting a list of terms for the first free variables of a term.
subst :: [Term] -> Term -> Term
subst ts t = concatMap sub t
  where
    sub m | m < length ts = ts !! m
	  | otherwise	  = [ m - length ts ]

{-
  Now the lookup functions. First we should think about what results we want to
  get.  There are really two problems: first, to look up a definition with all
  the right free variables, and second, to instantiate these free variables to
  the proper things from the context. Let's solve only the first problem to
  begin with. For this, the current context is irrelevant so we can look at the
  problem globally.

  Example:

    module T Φ where
      module A Δ where
	f = e
      module B Γ = A us
      module C Θ where
	module D = B vs
      module E = C ws

    Here we have

      ΦΔ ⊢ e
      ΦΓ ⊢ us
      ΦΘ ⊢ vs
      Φ  ⊢ ws

    When looking up a name we get a definition which is valid in the
    context inside its module:

      T.A.f   --> ΦΔ ⊢ e
      T.B.f   --> ΦΓ ⊢ e↑(Γ,Δ)[us/Δ]		    -- ΦΓΔ ⊢ e↑(Γ,Δ)
      T.C.D.f --> ΦΘ ⊢ e↑(Γ,Δ)[us/Δ]↑(Θ,Γ)[vs/Γ]    -- ΦΘΓ ⊢ e↑(Γ,Δ)[us/Δ]↑(Θ,Γ)
      T.E.D.f --> Φ  ⊢ e↑(Γ,Δ)[us/Δ]↑(Θ,Γ)[vs/Γ][ws/Θ]

    Notation: e↑(Γ,Δ) = raiseByFrom (length Γ) (length Δ) e
	      e[us/Δ] = subst us e  -- requires ΓΔ ⊢ e, for some Γ

  To accomplish this we need only modify lookupModule to return a module with
  properly abstracted and instantiated definitions. So for our example:

    T.A --> Expl ΦΔ (f ↦ e) ∅
    T.B --> Expl ΦΓ (f ↦ e)↑(Γ,Δ)[us/Δ] ∅
    T.C --> Expl ΦΘ

  Would it be simpler to talk about subsitutions?
    ( γ : Γ -> Δ means Γ ⊢ γ : Δ and so Δ ⊢ t ==> Γ ⊢ tγ )
  We would have us : ΦΓ -> ΦΔ and vs : ΦΘ -> ΦΓ, except we would have to pad us
  and vs with appropriate identities. Maybe.. yes.

  If we make telescope always include parameters to parent module we can make
  the signature flat again. We'll need to expand telescopes and module
  applications when typechecking. So this exercise served only to reveal the
  fact that we don't need it...

-}

-- Example ----------------------------------------------------------------

{-
  module T Φ where
    module A Δ where
      f = e
    module B Γ = A us
    module C Θ where
      module D = B vs
    module E = C ws
-}
sig :: Sig
sig "T" = Expl phi defT modT
  where
    defT x   = noDef x "T"
    modT "A" = Expl delta defA modA
      where
	defA "f" = e
	defA  x  = noDef x "T.A"
	modA  x  = noMod x "T.A"
    modT "B" = Impl gamma ["T","A"] us
    modT "C" = Expl theta defC modC
      where
	defC  x  = noDef x "T.C"
	modC "D" = Impl [] ["T","B"] vs
	modC  x  = noMod x "T.C"
    modT "E" = Impl gamma ["T","C"] ws
    modT  x  = noMod x "T"

    phi	  = [(),()]
    delta = [()]
    gamma = [(),(),()]
    theta = [()]

    us	  = [[4,3,2,1,0]]     -- ΦΓ ⊢ us : Δ
    vs	  = [[0],[1,2],[2,1]] -- ΦΘ ⊢ vs : Γ
    ws	  = [[0,0,1]]	      -- Φ  ⊢ ws : Θ

    e	  = [0,1,2]	      -- ΦΔ ⊢ e

    noDef x m = error $ "no definition " ++ x ++ " in " ++ show m
    noMod x m = error $ "no module " ++ x ++ " in " ++ show m

-- vim: sts=2 sw=2
