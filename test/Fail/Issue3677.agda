-- Andreas, 2025-12-17, issue #3677
-- The example is shrunk from a real-world case of Oskar (oskeri).
-- He said he stared 20 minutes at the error before finding the cause.

postulate
  ▸_        : (A       : Set) → Set
  _,_       : (A B     : Set) → Set
  ⟨_,_,_,_⟩ : (A B C D : Set) → Set
  _⊢_∷_     : (A B C   : Set) → Set
  Final     : (A       : Set) → Set

infixr 4 _,_

postulate
  foo :
    ∀ Δ H t ρ S A                   -- The forgotten "→" here is punished harshly.
    Δ ⊢ ⟨ H , t , ρ , S ⟩ ∷ A →
    ▸ ⟨ H , t , ρ , S ⟩ →
    Final ⟨ H , t , ρ , S ⟩

--   error: [AmbiguousParseForApplication]
--   Don't know how to parse ▸ ⟨ H , t , ρ , S ⟩. Could mean any one of:
--     ▸ ((((((((⟨ H) ,) t) ,) ρ) ,) S) ⟩)
--     ▸ (⟨ H , t , ρ , S ⟩)
--     (▸ (⟨ H)) , (t , (ρ , (S ⟩)))
--     (▸ (⟨ H)) , (t , (((ρ ,) S) ⟩))
--     (▸ (⟨ H)) , (((t ,) ρ) , (S ⟩))
--     (▸ (⟨ H)) , (((((t ,) ρ) ,) S) ⟩)
--     (▸ (((⟨ H) ,) t)) , (ρ , (S ⟩))
--     (▸ (((⟨ H) ,) t)) , (((ρ ,) S) ⟩)
--     (▸ (((((⟨ H) ,) t) ,) ρ)) , (S ⟩)
--   Operators used in the grammar:
--     ,         (infixr operator, level 4)  _,_
--     ▸         (prefix operator, level 20) ▸_
--     ⟨_,_,_,_⟩ (closed operator)           ⟨_,_,_,_⟩
-- + Identifiers used in the grammar that overlap with the operators:
-- +   , ⟨ ⟩
--   when scope checking ▸ ⟨ H , t , ρ , S ⟩

-- The +ses mark the new parts in the error.
