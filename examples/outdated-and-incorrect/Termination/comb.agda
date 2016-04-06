module comb where

infixr 50 _⟶_

data Ty : Set where
  ι : Ty
  _⟶_ : Ty -> Ty -> Ty

data Tm : Ty -> Set where
  K : {σ τ : Ty} -> Tm (σ ⟶ τ ⟶ σ)
  S : {σ τ ρ : Ty} -> Tm ((σ ⟶ τ ⟶ ρ) ⟶ (σ ⟶ τ) ⟶ σ ⟶ ρ)
  _$_ : {σ τ : Ty} -> Tm (σ ⟶ τ) -> Tm σ -> Tm τ

data Nf : Ty -> Set where
  Kⁿ : {σ τ : Ty} -> Nf (σ ⟶ τ ⟶ σ)
  Kⁿ¹ : {σ τ : Ty} -> Nf σ -> Nf (τ ⟶ σ)
  Sⁿ : {σ τ ρ : Ty} -> Nf ((σ ⟶ τ ⟶ ρ) ⟶ (σ ⟶ τ) ⟶ σ ⟶ ρ)
  Sⁿ¹ : {σ τ ρ : Ty} -> Nf (σ ⟶ τ ⟶ ρ) -> Nf ((σ ⟶ τ) ⟶ σ ⟶ ρ)
  Sⁿ² : {σ τ ρ : Ty} -> Nf (σ ⟶ τ ⟶ ρ) -> Nf (σ ⟶ τ) -> Nf (σ ⟶ ρ)

_$$_ : {σ τ : Ty} -> Nf (σ ⟶ τ) -> Nf σ -> Nf τ
Kⁿ      $$ x = Kⁿ¹ x
Kⁿ¹ x   $$ y = x
Sⁿ      $$ x = Sⁿ¹ x
Sⁿ¹ x   $$ y = Sⁿ² x y
Sⁿ² x y $$ z = (x $$ z) $$ (y $$ z)

nf : {σ : Ty} -> Tm σ -> Nf σ
nf K = Kⁿ
nf S = Sⁿ
nf (t $ u) = nf t $$ nf u

data _$ⁿ_⇓_ : {σ τ : Ty} -> Nf (σ ⟶ τ) -> Nf σ -> Nf τ -> Set where
  rKⁿ  : {σ τ : Ty} -> {x : Nf σ} -> Kⁿ {σ} {τ} $ⁿ x ⇓ Kⁿ¹ x
  rKⁿ¹ : {σ τ : Ty} -> {x : Nf σ} -> {y : Nf τ} -> Kⁿ¹ x $ⁿ y ⇓ x
  rSⁿ  : {σ τ ρ : Ty} -> {x : Nf (σ ⟶ τ ⟶ ρ)} -> Sⁿ $ⁿ x ⇓ Sⁿ¹ x
  rSⁿ¹ : {σ τ ρ : Ty} -> {x : Nf (σ ⟶ τ ⟶ ρ)} -> {y : Nf (σ ⟶ τ)} ->
    Sⁿ¹ x $ⁿ y ⇓ Sⁿ² x y
  rSⁿ² : {σ τ ρ : Ty} -> {x : Nf (σ ⟶ τ ⟶ ρ)} -> {y : Nf (σ ⟶ τ)} ->
    {z : Nf σ} -> {u : Nf (τ ⟶ ρ)} -> x $ⁿ z ⇓ u -> {v : Nf τ} ->
    y $ⁿ z ⇓ v -> {w : Nf ρ} -> u $ⁿ v ⇓ w -> Sⁿ² x y $ⁿ z ⇓ w

data _⇓_ : {σ : Ty} -> Tm σ -> Nf σ -> Set where
  rK : {σ τ : Ty} -> K {σ} {τ} ⇓ Kⁿ
  rS : {σ τ ρ : Ty} -> S {σ} {τ} {ρ} ⇓ Sⁿ
  r$ : {σ τ : Ty} -> {t : Tm (σ ⟶ τ)} -> {f : Nf (σ ⟶ τ)} -> t ⇓ f ->
    {u : Tm σ} -> {a : Nf σ} -> u ⇓ a -> {v : Nf τ} -> f $ⁿ a ⇓ v  ->
    t $ u ⇓ v

data _==_ {A : Set}(a : A) : {B : Set} -> (b : B) -> Set where
  refl : a == a

data Σ {A : Set}(B : A -> Set) : Set where
  sig : (a : A) -> (b : B a) -> Σ B

σ₀ : {A : Set} -> {B : A -> Set} -> Σ B -> A
σ₀ (sig x _) = x

σ₁ : {A : Set} -> {B : A -> Set} -> (s : Σ B) -> B (σ₀ s)
σ₁ (sig _ y) = y


_$$⁼_&_ : {σ τ : Ty} -> (f : Nf (σ ⟶ τ)) -> (a : Nf σ) -> {n : Nf τ} ->
  f $ⁿ a ⇓ n ->     Σ \(n' : Nf τ) -> n' == n
Kⁿ      $$⁼ x & rKⁿ  = sig (Kⁿ¹ x) refl
Kⁿ¹ x   $$⁼ y & rKⁿ¹ = sig x refl
Sⁿ      $$⁼ x & rSⁿ  = sig (Sⁿ¹ x) refl
Sⁿ¹ x   $$⁼ y & rSⁿ¹ = sig (Sⁿ² x y) refl
Sⁿ² x y $$⁼ z & (rSⁿ² p q r) with x $$⁼ z & p | y $$⁼ z & q
Sⁿ² x y $$⁼ z & (rSⁿ² p q r)  |   sig u refl  | sig v refl with u $$⁼ v & r
Sⁿ² x y $$⁼ z & (rSⁿ² p q r)  |   sig u refl  | sig v refl  |   sig w refl =
  sig w refl

nf⁼ : {σ : Ty} -> (t : Tm σ) -> {n : Nf σ} -> t ⇓ n ->
  Σ \(n' : Nf σ) -> n' == n
nf⁼ K rK = sig Kⁿ refl
nf⁼ S rS = sig Sⁿ refl
nf⁼ (t $ u) (r$ p q r) with nf⁼ t p    | nf⁼ u q
nf⁼ (t $ u) (r$ p q r)  |   sig f refl | sig a refl with f $$⁼ a & r
nf⁼ (t $ u) (r$ p q r)  |   sig f refl | sig a refl  |   sig v refl =
  sig v refl

proof : {σ : Ty} -> (t : Tm σ) -> Σ \(n : Nf σ) -> t ⇓ n
proof = {! !}

nf⇓ :  {σ : Ty} -> Tm σ -> Nf σ
nf⇓ t = σ₀ (nf⁼ t (σ₁ (proof t)))

