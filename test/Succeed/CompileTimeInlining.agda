------------------------------------------------------------------------
-- A small definition of a dependently typed language, using the
-- technique from McBride's "Outrageous but Meaningful Coincidences"
------------------------------------------------------------------------

-- Inlining saves a lot of memory. Test with +RTS -M100M
-- The inlining of zero and suc in raw-category at the end is the most
-- important.

{-# OPTIONS --type-in-type #-}

module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- Prelude

data ⊥ : Set where

⊥-elim : ⊥ → {A : Set} → A
⊥-elim ()

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

uncurry : {A : Set} {B : A → Set} {C : Σ A B → Set} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f p = f (fst p) (snd p)

infixr 2 _×_
_×_ : Set → Set → Set
_×_ A B = Σ A (λ _ → B)

------------------------------------------------------------------------
-- A universe

data U : Set

El : U → Set

data U where
  set   : U
  el    : Set → U
  sigma : (a : U) → (El a → U) → U
  pi    : (a : U) → (El a → U) → U

El set         = Set
El (el A)      = A
El (sigma a b) = Σ (El a) (λ x → El (b x))
El (pi a b)    = (x : El a) → El (b x)

-- Abbreviations.

fun : U → U → U
fun a b = pi a (λ _ → b)

times : U → U → U
times a b = sigma a (λ _ → b)

-- -- Example.

------------------------------------------------------------------------
-- Contexts

-- Contexts.

data Ctxt : Set

-- Types.

Ty : Ctxt → Set

-- Environments.

Env : Ctxt → Set

data Ctxt where
  empty : Ctxt
  snoc  : (G : Ctxt) → Ty G → Ctxt

Ty G = Env G → U

Env empty      = ⊤
Env (snoc G s) = Σ (Env G) (λ g → El (s g))

-- Variables (deBruijn indices).

Var : ∀ G → Ty G → Set
Var empty      t = ⊥
Var (snoc G s) t =
  Either ((λ g → s (fst g)) ≡ t)
         (Σ _ (λ u → (λ g → u (fst g)) ≡ t × Var G u))

zero : ∀ {G s} → Var (snoc G s) (λ g → s (fst g))
zero = left refl

suc : ∀ {G s t} → (x : Var G t) → Var (snoc G s) (λ g → t (fst g))
suc x = right (_ , refl , x)

-- A lookup function.

lookup : ∀ G (s : Ty G) → Var G s → (g : Env G) → El (s g)
lookup empty      _ absurd     _ = ⊥-elim absurd
lookup (snoc vs v) _ (left refl) g = snd g
lookup (snoc vs v) t (right (_ , refl , x))  g = lookup _ _ x (fst g)

------------------------------------------------------------------------
-- A language

-- Syntax for types.

data Type (G : Ctxt) (s : Ty G) : Set

-- Terms.

data Term (G : Ctxt) (s : Ty G) : Set

-- The semantics of a term.

eval : ∀ {G s} → Term G s → (g : Env G) → El (s g)

data Type G s where
  set''   : s ≡ (λ _ → set) → Type G s
  el''    : (x : Term G (λ _ → set)) →
            (λ g → el (eval {s = λ _ → set} x g)) ≡ s →
            Type G s
  sigma'' : {t : _} {u : _} →
            Type G t →
            Type (snoc G t) u →
            (λ g → sigma (t g) (λ v → u (g , v))) ≡ s →
            Type G s
  pi''    : {t : _} {u : _} →
            Type G t →
            Type (snoc G t) u →
            (λ g → pi (t g) (λ v → u (g , v))) ≡ s →
            Type G s

data Term G s where
  var   : Var G s → Term G s
  lam'' : {t : _} {u : _} →
          Term (snoc G t) (uncurry u) →
          (λ g → pi (t g) (λ v → u g v)) ≡ s →
          Term G s
  app'' : {t : _} {u : (g : Env G) → El (t g) → U} →
          Term G (λ g → pi (t g) (λ v → u g v)) →
          (t2 : Term G t) →
          (λ g → u g (eval t2 g)) ≡ s →
          Term G s

eval (var x)            g = lookup _ _ x g
eval (lam'' t refl)     g = λ v → eval t (g , v)
eval (app'' t1 t2 refl) g = eval t1 g (eval t2 g)

-- Abbreviations.

set' : {G : Ctxt} → Type G (λ _ → set)
set' = set'' refl

el' : {G : Ctxt}
      (x : Term G (λ _ → set)) →
      Type G (λ g → el (eval {G} {λ _ → set} x g))
el' x = el'' x refl

sigma' : {G : Ctxt} {t : Env G → U} {u : Env (snoc G t) → U} →
         Type G t →
         Type (snoc G t) u →
         Type G (λ g → sigma (t g) (λ v → u (g , v)))
sigma' s t = sigma'' s t refl

pi' : {G : _} {t : _} {u : _} →
      Type G t →
      Type (snoc G t) u →
      Type G (λ g → pi (t g) (λ v → u (g , v)))
pi' s t = pi'' s t refl

lam : {G : _} {t : _} {u : _} →
      Term (snoc G t) (uncurry u) →
      Term G (λ g → pi (t g) (λ v → u g v))
lam t = lam'' t refl

app : {G : _} {t : _} {u : (g : Env G) → El (t g) → U} →
      Term G (λ g → pi (t g) (λ v → u g v)) →
      (t2 : Term G t) →
      Term G (λ g → u g (eval t2 g))
app t1 t2 = app'' t1 t2 refl

-- Example.

raw-categoryU : U
raw-categoryU =
  sigma set (λ obj →
  sigma (fun (el obj) (fun (el obj) set)) (λ hom →
  times
    (pi (el obj) (λ x → el (hom x x)))
    (pi (el obj) (λ x → el (hom x x)))))

raw-category : Type empty (λ _ → raw-categoryU)
raw-category =
     -- Objects.
   sigma' set'
     -- Morphisms.
  (sigma' (pi' (el' (var zero)) (pi' (el' (var (suc zero))) set'))
     -- Identity.
  (sigma' (pi' (el' (var (suc zero)))
               (el' (app (app (var (suc zero)) (var zero)) (var zero))))
          (pi' (el' (var (suc (suc zero))))
               (el' (app (app (var (suc (suc zero))) (var zero)) (var zero))))))
