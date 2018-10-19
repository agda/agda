..
  ::
  module language.generalization-of-declared-variables where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

************************************
Generalization of Declared Variables
************************************

Variables to be generalized can declared with the keyword ``variable``.
For example:

::

  postulate
        Con : Set

  variable
        Γ Δ Θ : Con


Declared variables are automatically generalized in type signatures:

::

  postulate
        Sub : Con → Con → Set

        id  : Sub Γ Γ
    --  -- equivalent to
    --  id  : {Γ : Con} → Sub Γ Γ

        _∘_ : Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
    --  -- equivalent to
    --  _∘_ : {Γ Δ Θ : Con} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ

Note that each type signature has a separate copy of its declared variables,
so ``id`` and ``_∘_`` refer to two different ``Γ`` named variables.

The following rules are used to place the generalized variables:

    - Generalized variables are placed in the front of the type signatures.
    - Variables defined sooner are placed before variables defined later.
      (The dependencies between the variables are obeyed. The current implementation
      uses "smallest-numbered available vertex first" topological sorting to determine
      the exact order.)

``variable`` allows metavariables in the type of declared variables.
For example:

::

  postulate
        Ty  : Con → Set
        _▹_ : (Γ : Con) → Ty Γ → Con

  variable
        A : Ty _       -- note the underscore here

  postulate
        π₁ : Sub Γ (Δ ▹ A) → Sub Γ Δ
    --  -- equivalent to
    --  π₁ : {Γ Δ : Con}{A : Ty Δ} → Sub Γ (Δ ▹ A) → Sub Γ Δ
    --  -- note that the metavariable was solved with Δ

Note that each type signature has a separate copy of such metavariables,
so the underscore in ``Ty _`` can be solved differently for each type signature
which mentions ``A``.

Unsolved metavariables originated from ``variable`` are generalized.
For example:

::

  variable
        σ δ ν : Sub _ _   -- metavariables: σ.1, σ.2, δ.1, δ.2, ν.1, ν.2

  postulate
        ass : (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
    --  -- equivalent to
    --  ass : {σ.1 σ.2 δ.1 ν.1 : Con}
    --        {σ : Sub σ.1 σ.2}{δ : Sub δ.1 σ.1}{ν : Sub ν.1 δ.1}
    --      → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

Note that ``δ.2`` was solved with ``σ.1`` and ``ν.2`` was solved with ``δ.1``.
If two generalizable metavariables can be solved with each-other then
the metavariable defined later will be eliminated.

Hierarchical names like ``δ.2`` are used so one can track the origin of
the metavariables.
Currently it is not allowed to use hierarchical names when giving parameters
to functions, see Issue #3280 <https://github.com/agda/agda/issues/3280>.

Name hints of parameters are used for naming generalizable metavariables too:

::

  postulate
        Sub' : (Γ Δ : Con) → Set   -- name hints for parameters of Sub'

  variable
        θ : Sub' _ _   -- metavariables: θ.Γ, θ.Δ

If a generalizable metavariable M is solved with term T then M is not
generalized, but metavariables in T became candidates for generalization.

It is allowed to nest declared variables.
For example:

::

  variable
        ℓ : Level     -- let ℓ denote a level
        S : Set ℓ     -- let A denote a set at a level ℓ

  postulate
        f : S → Set ℓ
    --  -- equivalent to
    --  f : {ℓ ℓ' : Level}{S : Set ℓ'} → S → Set ℓ

Issues related to this feature are marked with `generalize` in the issue tracker:
https://github.com/agda/agda/labels/generalize

