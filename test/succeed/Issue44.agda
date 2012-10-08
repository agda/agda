{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.polarity:10 #-}
module Issue44 where

data Ty : Set where
  ι : Ty
  _⇒_ : Ty -> Ty -> Ty

data Con : Set where
  ε : Con
  _<_ : Con -> Ty -> Con

data Var : Con -> Ty -> Set where
  vZ : forall {Γ σ} -> Var (Γ < σ) σ
  vS : forall {Γ σ}{τ : Ty} -> Var Γ σ -> Var (Γ < τ) σ

{-
stren : forall {Γ σ} -> Var Γ σ -> Con
stren (vZ {Γ}) = Γ
stren (vS {τ = τ} v) = stren v < τ

_/_ : forall Γ {σ} -> Var Γ σ -> Con
Γ / v = stren v
-}

-- However if I make stren a local function:

_/_ : forall Γ {σ} -> Var Γ σ -> Con
Γ / v = stren v where
  stren : forall {Γ σ} -> Var Γ σ -> Con
  stren (vZ {Γ}) = Γ
  stren (vS {τ = τ} v) = stren v < τ

thin : forall {Γ σ τ}(v : Var Γ σ) -> Var (Γ / v) τ -> Var Γ τ
thin vZ v' = vS v'
thin (vS v) vZ = vZ
thin (vS v) (vS v') = vS (thin v v')
