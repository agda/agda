
module CwF where

open import Setoid
open EqChain

infixr 30 _⇒_
infixl 50 _/_ _/ˢ_
infixr 45 _◄_
infixl 45 _▷_

Cxt : Set
Cxt = Setoid

_⇒_ : Cxt -> Cxt -> Set
Γ ⇒ Δ = El (Γ ==> Δ)

Type : Cxt -> Set
Type Γ = Fam Γ

_/_ : {Γ Δ : Cxt} -> Type Γ -> (Δ ⇒ Γ) -> Type Δ
A / σ = A ○ σ

lem-/id : {Γ : Cxt}{A : Type Γ} -> A / id == A
lem-/id = lem-○-id

Term : (Γ : Cxt) -> Type Γ -> Set
Term Γ A = El (Π Γ A)

_◄_ : {Γ : Cxt}{A B : Type Γ} -> B == A -> Term Γ A -> Term Γ B
B=A ◄ u = eqΠ refl B=A << u

_/ˢ_ : {Γ Δ : Cxt}{A : Type Γ} -> Term Γ A -> (σ : Δ ⇒ Γ) -> Term Δ (A / σ)
u /ˢ σ = u ∘ σ

_▷_ : (Γ : Cxt) -> Type Γ -> Cxt
Γ ▷ A = Σ Γ A

wk : {Γ : Cxt}(A : Type Γ) -> Γ ▷ A ⇒ Γ
wk A = ƛ fst \ x y x=y -> fst-eq x=y

vz : {Γ : Cxt}(A : Type Γ) -> Term (Γ ▷ A) (A / wk A)
vz A = ƛ snd \ x y x=y -> snd-eq x=y

ext : {Γ Δ : Cxt}(A : Type Γ)(σ : Δ ⇒ Γ)(u : Term Δ (A / σ)) -> Δ ⇒ Γ ▷ A
ext A σ u = ƛ (\x -> (σ # x , u # x))
               \x y x=y -> eqInΣ refl (#-cong-R σ x=y) (#-cong-R u x=y)

lem-/-· : {Γ Δ Θ : Cxt}(A : Type Γ)(σ : Δ ⇒ Γ)(δ : Θ ⇒ Δ) ->
          A / σ · δ == A / σ / δ
lem-/-· A σ δ = eqFam refl \x y x=y ->
  !-cong-R A (sym (cast-id' _ (#-cong-R σ (#-cong-R δ (cast-id' _ (sym x=y)))))) 

lem-wk-∘-ext : {Γ Δ : Cxt}(A : Type Δ)(σ : Γ ⇒ Δ)(u : Term Γ (A / σ)) ->
            wk A ∘ ext A σ u == σ
lem-wk-∘-ext A (ƛ σ pσ) u = eqInΠ refl pσ

lem-vz-/-ext : {Γ Δ : Cxt}(A : Type Δ)(σ : Γ ⇒ Δ)(u : Term Γ (A / σ)) ->
               vz A /ˢ (ext A σ u) == u
lem-vz-/-ext A σ (ƛ u pu) = eqInΠ refl pu

-- (σ , u) ∘ δ == (σ ∘ δ , u / δ)
lem-ext-∘ : {Γ Δ Θ : Cxt}{A : Type Γ}(σ : Δ ⇒ Γ)(δ : Θ ⇒ Δ)(u : Term Δ (A / σ)) ->
            ext A σ u · δ == ext A (σ · δ) (lem-/-· A σ δ ◄ u /ˢ δ)
lem-ext-∘ σ δ u = eqInΠ refl \x y x=y ->
  eqInΣ refl
    (cast-irr _ _ (#-cong-R σ (#-cong-R δ (cast-irr _ _ x=y))))
    (cast-irr _ _ (#-cong-R u (#-cong-R δ (cast-irr _ _ x=y))))

<_> : {Γ : Cxt}{A : Type Γ} -> Term Γ A -> Γ ⇒ Γ ▷ A
< u > = ext _ id (lem-○-id ◄ u)

lift : {Γ Δ : Cxt}(A : Type Γ)(σ : Δ ⇒ Γ) -> Δ ▷ (A / σ) ⇒ Γ ▷ A
lift A σ = ƛ (\x -> σ # fst x , snd x)
              \x y x=y -> eqInΣ refl (#-cong-R σ (fst-eq x=y)) (snd-eq x=y)

curryFam : {A : Setoid}{F : Fam A} -> Fam (Σ A F) -> (x : El A) -> Fam (F ! x)
curryFam G x = fam (\y -> G ! (x , y))
                   \z w z=w -> !-cong-R G (eqInΣ refl refl z=w)

Pi : {Γ : Cxt}(A : Type Γ)(B : Type (Γ ▷ A)) -> Type Γ
Pi A B = fam (\x -> Π (A ! x) (curryFam B x))
              \x y x=y ->
                eqΠ (!-cong-R A (sym x=y))
                    (eqFam (!-cong-R A (sym x=y)) \z w z=w ->
                            !-cong-R B (eqInΣ refl x=y z=w)
                    )

lem-Pi-/ : {Γ Δ : Cxt}(A : Type Γ)(B : Type (Γ ▷ A))(σ : Δ ⇒ Γ) ->
           Pi A B / σ == Pi (A / σ) (B / lift A σ)
lem-Pi-/ A B σ = eqFam refl \x y x=y ->
  eqΠ (Aσ-eq x=y)
      (eqFam (Aσ-eq x=y) \z w z=w ->
        !-cong-R B (eqInΣ refl (#-cong-R σ x=y) z=w)
      )
  where
    Aσ-eq : forall {x y} -> x == y -> A ! σ # y == A ! σ # x
    Aσ-eq x=y = !-cong-R A (#-cong-R σ (sym x=y))

lam : {Γ : Cxt}{A : Type Γ}{B : Type (Γ ▷ A)} -> Term (Γ ▷ A) B -> Term Γ (Pi A B)
lam {A = A} f =
  ƛ (\γ -> ƛ (\x -> f # (γ , x)) (prf₁ γ)) prf₂
  where
      prf₁ : forall γ x y x=y -> _
      prf₁ = \γ x y x=y -> #-cong-R f (eqInΣ refl refl x=y)

      prf₂ = \x y x=y ->
        eqInΠ (!-cong-R A (sym x=y)) \z w z=w ->
          #-cong-R f (eqInΣ refl x=y z=w)

app : {Γ : Cxt}(A : Type Γ)(B : Type (Γ ▷ A))
      (v : Term Γ (Pi A B))(u : Term Γ A) -> Term Γ (B / < u >)
app A B v u = ƛ (\γ -> prf₁ γ << v # γ # (u # γ)) prf₂
  where
      lem : forall γ -> < u > # γ == (γ , u # γ)
      lem γ = eqInΣ refl refl (#-cong (lem-○-id ◄ u) u (sym (cast-id _)) refl)

      prf₁ : forall γ -> (B / < u >) ! γ == B ! (γ , u # γ)
      prf₁ γ = !-cong-R B (lem γ)

      prf₂ = \x y x=y -> cast-irr _ _ (#-cong (v # x) (v # y)
                                              (#-cong-R v x=y)
                                              (#-cong-R u x=y)
                                      )

lem-β : {Γ : Cxt}(A : Type Γ)(B : Type (Γ ▷ A))
        (v : Term (Γ ▷ A) B)(u : Term Γ A) ->
        app A B (lam v) u == v /ˢ < u >
lem-β A B v u = eqInΠ refl \x y x=y ->
  sym (cast-id' _
    (#-cong-R v
      (eqInΣ refl (sym x=y)
        (#-cong (lem-○-id ◄ u) u (sym (cast-id _)) (sym x=y)))
      )
    )

-- The stack blows when trying to prove η.
-- I'm not sure it does anymore, but I have no idea how to prove η,
-- I struggled just giving the type.
-- lem-η : {Γ : Cxt}(A : Type Γ)(B : Type (Γ ▷ A))
--         (v : Term Γ (Pi A B)) →
--         v == lam (app (A / wk A) (B / lift A (wk A)) (sym (lem-Pi-/ A B (wk A)) ◄ v /ˢ wk A) (vz A))
-- lem-η {Γ} A B (ƛ f pf) =
--   eqInΠ =S=-refl λ γ δ γ=δ →
--   proof f γ ≡ ƛ (_#_ (f γ)) (λ _ _ → #-cong-R (f γ)) by η (f γ)
--             ≡ _ by eqInΠ (!-cong-R A (sym γ=δ)) (λ x y x=y →
--     proof f γ # x
--       ≡ (_ << (_ << f (_ << δ))) # y by {!!}
--     qed)
--   qed
