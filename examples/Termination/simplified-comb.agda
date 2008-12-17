module JamesChapman where

infixr 50 _⟶_

data Ty : Set where
   ι : Ty
   _⟶_ : Ty -> Ty -> Ty

data Tm : Ty -> Set where
   _$_ : {σ τ : Ty} -> Tm (σ ⟶ τ) -> Tm σ -> Tm τ

data Nf : Ty -> Set where

data _↓_ : {σ : Ty} -> Tm σ -> Nf σ -> Set where
   r$ : {σ τ : Ty} -> {t : Tm (σ ⟶ τ)} -> {f : Nf (σ ⟶ τ)} -> t ↓ f ->
     {u : Tm σ} -> {a : Nf σ} -> u ↓ a -> {v : Nf τ} ->
     t $ u ↓ v

nf* : {σ : Ty} -> (t : Tm σ) -> {n : Nf σ} -> t ↓ n -> Set
nf* .{τ} (_$_ {σ} {τ} t u) {v} (r$ {f = f} p q) with nf* {σ ⟶ τ} t {f} p
nf* (t $ u) (r$ p q)  |   _ = Ty
