module Issue347 where
import Common.Irrelevance  

{- Dan Doel, 2010-10-09

This is a boiling down of a problem encountered by Eric Mertens. It
seems the unifier will make up values for records without bothering
with irrelevant fields: -}

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

⊥-elimⁱ : {A : Set} → .⊥ → A
⊥-elimⁱ ()

module Bad where
  record ○ (A : Set) : Set where
    constructor poof
    field
      .inflate : A

  open ○

  -- This, for some reason, doesn't. Apparently it thinks it can
  -- make up records without bothering to infer the irrelevant fields.
  evil : ∀ A → A
  evil A = ⊥-elimⁱ (inflate _)

  -- the meta var  ?a : Squash A  eta-expands to
  -- ?a = poof Bot ?b
  -- meta var ?b should be left over


