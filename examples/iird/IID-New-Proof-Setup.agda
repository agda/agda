
module IID-New-Proof-Setup where

open import LF
open import Identity
open import IID
open import IIDr
open import DefinitionalEquality

OPg : Set -> Set1
OPg I = OP I I

-- Encoding indexed inductive types as non-indexed types.
ε : {I : Set}(γ : OPg I) -> OPr I
ε (ι i)     j = σ (i == j) (\_ -> ι ★)
ε (σ A γ)   j = σ A (\a -> ε (γ a) j)
ε (δ H i γ) j = δ H i (ε γ j)


-- Adds a reflexivity proof.
g→rArgs : {I : Set}(γ : OPg I)(U : I -> Set)
	      (a : Args γ U) ->
	      rArgs (ε γ) U (index γ U a)
g→rArgs (ι e)     U arg	= (refl , ★)
g→rArgs (σ A γ)   U arg = (π₀ arg , g→rArgs (γ (π₀ arg)) U (π₁ arg))
g→rArgs (δ H i γ) U arg = (π₀ arg , g→rArgs γ U (π₁ arg))
