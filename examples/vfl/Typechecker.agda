
module Typechecker where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

_+_ : Nat -> Nat -> Nat
zero   + m = m
suc n  + m = suc (n + m)

data Fin : Nat -> Set where
  f0 : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

infixl 30 _::_ _++_

data Vect (A : Set) : Nat -> Set where
  ε    : Vect A zero
  _::_ : {n : Nat} -> Vect A n -> A -> Vect A (suc n)

fs^ : {n : Nat}(m : Nat) -> Fin n -> Fin (m + n)
fs^ zero    i = i
fs^ (suc m) i = fs (fs^ m i)

_++_ : {A : Set}{n m : Nat} -> Vect A n -> Vect A m -> Vect A (m + n)
xs ++ ε         = xs
xs ++ (ys :: y) = (xs ++ ys) :: y

data Chop {A : Set} : {n : Nat} -> Vect A n -> Fin n -> Set where
  chopGlue : {m n : Nat}(xs : Vect A n)(x : A)(ys : Vect A m) ->
             Chop (xs :: x ++ ys) (fs^ m f0)

chop : {A : Set}{n : Nat}(xs : Vect A n)(i : Fin n) -> Chop xs i
chop ε         ()
chop (xs :: x) f0 = chopGlue xs x ε
chop (xs :: y) (fs i) with chop xs i
chop (.(xs :: x ++ ys) :: y) (fs .(fs^ m f0))
  | chopGlue {m} xs x ys = chopGlue xs x (ys :: y)

infixr 40 _⊃_

data Simp : Set where
  o   : Simp
  _⊃_ : Simp -> Simp -> Simp

infix 20 Simp-_

data Simp-_ : Simp -> Set where
  neqo : Simp -> Simp -> Simp- o
  neq⊃ : {S T : Simp} -> Simp- (S ⊃ T)
  neqT : {S T : Simp}(T' : Simp- T) -> Simp- (S ⊃ T)
  neqS : {S : Simp}{T₁ : Simp}(S' : Simp- S)(T₂ : Simp) -> Simp- (S ⊃ T₁)

infixl 60 _∖_

_∖_ : (S : Simp) -> Simp- S -> Simp
.o       ∖ neqo S T        = S ⊃ T
.(_ ⊃ _) ∖ neq⊃            = o
.(S ⊃ T) ∖ neqT {S}{T}  T' = S ⊃ T ∖ T'
.(S ⊃ _) ∖ neqS {S} S' T₂  = S ∖ S' ⊃ T₂

data SimpEq? (S : Simp) : Simp -> Set where
  simpSame : SimpEq? S S
  simpDiff : (T : Simp- S) -> SimpEq? S (S ∖ T)

simpEq? : (S T : Simp) -> SimpEq? S T
simpEq? o o = simpSame
simpEq? o (S ⊃ T) = simpDiff (neqo S T)
simpEq? (S ⊃ T) o = simpDiff neq⊃
simpEq? (S₁ ⊃ T₁) (S₂ ⊃ T₂) with simpEq? S₁ S₂
simpEq? (S ⊃ T₁)  (.S ⊃ T₂)        | simpSame with simpEq? T₁ T₂
simpEq? (S ⊃ T)   (.S ⊃ .T)        | simpSame | simpSame    = simpSame
simpEq? (S ⊃ T)   (.S ⊃ .(T ∖ T')) | simpSame | simpDiff T' = simpDiff (neqT T')
simpEq? (S ⊃ T₁)  (.(S ∖ S') ⊃ T₂) | simpDiff S' = simpDiff (neqS S' T₂)

data Term : Nat -> Set where
  var : {n : Nat} -> Fin n -> Term n
  app : {n : Nat} -> Term n -> Term n -> Term n
  lam : {n : Nat} -> Simp -> Term (suc n) -> Term n

data Good : {n : Nat} -> Vect Simp n -> Simp -> Set where
  gVar : {n m : Nat}(Γ : Vect Simp n)(T : Simp)(Δ : Vect Simp m) ->
         Good (Γ :: T ++ Δ) T
  gApp : {n : Nat}{Γ : Vect Simp n}{S T : Simp} ->
         Good Γ (S ⊃ T) -> Good Γ S -> Good Γ T
  gLam : {n : Nat}{Γ : Vect Simp n}(S : Simp){T : Simp} ->
         Good (Γ :: S) T -> Good Γ (S ⊃ T)

g : {n : Nat}{Γ : Vect Simp n}(T : Simp) -> Good Γ T -> Term n
g T        (gVar{n}{m} Γ .T Δ) = var (fs^ m f0)
g T        (gApp f s)          = app (g _ f) (g _ s)
g .(S ⊃ _) (gLam S t)          = lam S (g _ t)

data Bad {n : Nat}(Γ : Vect Simp n) : Set where
  bNonFun   : Good Γ o -> Term n -> Bad Γ
  bMismatch : {S T : Simp}(S' : Simp- S) ->
              Good Γ (S ⊃ T) -> Good Γ (S ∖ S') -> Bad Γ
  bArg      : {S T : Simp} -> Good Γ (S ⊃ T) -> Bad Γ -> Bad Γ
  bFun      : Bad Γ -> Term n -> Bad Γ
  bLam      : (S : Simp) -> Bad (Γ :: S) -> Bad Γ

b : {n : Nat}{Γ : Vect Simp n} -> Bad Γ -> Term n
b (bNonFun f s)     = app (g o f) s
b (bMismatch _ f s) = app (g _ f) (g _ s)
b (bArg f s)        = app (g _ f) (b s)
b (bFun f s)        = app (b f) s
b (bLam S t)        = lam S (b t)

data TypeCheck? {n : Nat}(Γ : Vect Simp n) : Term n -> Set where
  good : (T : Simp)(t : Good Γ T) -> TypeCheck? Γ (g T t)
  bad  : (t : Bad Γ) -> TypeCheck? Γ (b t)

typeCheck? : {n : Nat}(Γ : Vect Simp n)(t : Term n) -> TypeCheck? Γ t
typeCheck? Γ (var i)   with chop Γ i
typeCheck? .(Γ :: T ++ Δ) (var ._) | chopGlue Γ T Δ = good T (gVar Γ T Δ)

typeCheck? Γ (app f s) with typeCheck? Γ f
typeCheck? Γ (app .(g (S ⊃ T) f) s) | good (S ⊃ T) f with typeCheck? Γ s
typeCheck? Γ (app .(g (S ⊃ T) f) .(g S' s))
             | good (S ⊃ T) f | good S' s with simpEq? S S'
typeCheck? Γ (app .(g (S ⊃ T) f) .(g S s))
             | good (S ⊃ T) f | good .S s        | simpSame    = good T (gApp f s)
typeCheck? Γ (app .(g (S ⊃ T) f) .(g (S ∖ S') s))
             | good (S ⊃ T) f | good .(S ∖ S') s | simpDiff S' = bad (bMismatch S' f s)
typeCheck? Γ (app .(g (S ⊃ T) f) .(b s))
             | good (S ⊃ T) f | bad s     = bad (bArg f s)
typeCheck? Γ (app .(g o f) s)       | good o f       = bad (bNonFun f s)
typeCheck? Γ (app .(b f) s)         | bad f          = bad (bFun f s)

typeCheck? Γ (lam S t) with typeCheck? (Γ :: S) t
typeCheck? Γ (lam S .(g T t)) | good T t = good (S ⊃ T) (gLam S t)
typeCheck? Γ (lam S .(b t))   | bad t    = bad (bLam S t)