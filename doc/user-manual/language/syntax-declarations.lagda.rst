..
  ::
  module language.syntax-declarations where

.. _syntax-declarations:

*******************
Syntax Declarations
*******************

.. note::
   This is a stub

It is now possible to declare user-defined syntax that binds
identifiers. Example:

..
  ::

  postulate
   ℕ ⊤ : Set
   suc : ℕ → ℕ
..
  ::

  module First where

::

    postulate
      State  : Set → Set → Set
      put    : ∀ {S} → S → State S ⊤
      get    : ∀ {S} → State S S
      return : ∀ {A S} → A → State S A
      bind   : ∀ {A B S} → State S B → (B → State S A) → State S A

    syntax bind e₁ (λ x → e₂) = x ← e₁ , e₂

    increment : State ℕ ⊤
    increment = x ← get ,
                put (suc x)

The syntax declaration for ``bind`` implies that ``x`` is in scope in
``e₂``, but not in ``e₁``.

You can give fixity declarations along with syntax declarations:


..
  ::

  module Second where
    postulate
      State  : Set → Set → Set
      bind   : ∀ {A B S} → State S B → (B → State S A) → State S A

::


    infixr 40 bind
    syntax bind e₁ (λ x → e₂) = x ← e₁ , e₂

The fixity applies to the syntax, not the name; syntax declarations
are also restricted to ordinary, non-operator names. The following
declaration is disallowed:

.. code-block:: agda

  syntax _==_ x y = x === y

Syntax declarations must also be linear; the following declaration
is disallowed:

.. code-block:: agda

  syntax wrong x = x + x

Syntax declarations can have implicit arguments. For example:

::

  id : ∀ {a}{A : Set a} -> A -> A
  id x = x

  syntax id {A} x = x ∈ A
