module Bug where

data A : Set where
  a : A

h : A -> A
h a = a

data B : A -> Set where
  b : (x : A) -> B (h x)

data _==_ : {x₁ x₂ : A} -> B x₁ -> B x₂ -> Set where
  eqb : {x : A} -> b x == b x

-- The problem here is that we get the constraint h x = h x, which when x is a
-- meta variable we don't solve. This constraint blocks the solution y := b x
-- and so we don't see that y should be dotted. Either explicitly dotting y or
-- binding x removes the problem.
bad : {x : A}{y : B x} -> y == y -> A
bad eqb = ?
-- bad .{h x} .{b x} (eqb {x}) = ?    -- works
-- bad .{y = _} eqb            = ?    -- works
-- bad (eqb {_})               = ?    -- works

-- The above example is solved by checking syntactic equality on blocked terms.
-- This doesn't work below:

infixl 70 _/_
infixl 50 _▻_
infix  40 _∋_ _⊢ _⇒_ _≛_ _≈∋_

mutual

  data Ctxt : Set where
    _▻_ : (Γ : Ctxt) -> Γ ⊢ -> Ctxt

  data _⊢ : (Γ : Ctxt) -> Set where
    ✶  : {Γ : Ctxt} -> Γ ⊢

  data _⇒_ : Ctxt -> Ctxt -> Set where
    wk : {Γ : Ctxt} (σ : Γ ⊢) -> Γ ⇒ Γ ▻ σ

  data _∋_ : (Γ : Ctxt) -> Γ ⊢ -> Set where
    vz : {Γ : Ctxt} (τ : Γ ⊢) -> Γ ▻ τ ∋ τ / wk τ

  _/_ : {Γ Δ : Ctxt} -> Γ ⊢ -> Γ ⇒ Δ -> Δ ⊢
  ✶ / ρ = ✶

data _≛_ : {Γ¹ Γ² : Ctxt} -> Γ¹ ⊢ -> Γ² ⊢ -> Set where

data _≈∋_ :  {Γ¹ Γ² : Ctxt} {τ¹ : Γ¹ ⊢} {τ² : Γ² ⊢}
          -> Γ¹ ∋ τ¹ -> Γ² ∋ τ² -> Set where

  vzCong : {Γ¹ : Ctxt} {τ¹ : Γ¹ ⊢}
           {Γ² : Ctxt} {τ² : Γ² ⊢}
    -> τ¹ ≛ τ² -> vz τ¹ ≈∋ vz τ²

f : {Γ¹ : Ctxt} {σ¹ : Γ¹ ⊢} {v¹ : Γ¹ ∋ σ¹}
    {Γ² : Ctxt} {σ² : Γ² ⊢} {v² : Γ² ∋ σ²}
    {Γ³ : Ctxt} {σ³ : Γ³ ⊢} {v³ : Γ³ ∋ σ³}
  -> v¹ ≈∋ v² -> v² ≈∋ v³ -> v¹ ≈∋ v³
f (vzCong eqσ¹²) (vzCong eqσ²³) = ?


