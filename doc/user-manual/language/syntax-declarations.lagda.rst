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

    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,_
      field fst : A
            snd : B fst

    syntax Σ A (λ x → B) = [ x ∈ A ] × B

    witness : ∀ {A B} → [ x ∈ A ] × B → A
    witness (x , _) = x

The syntax declaration for ``Σ`` implies that ``x`` is in scope in
``B``, but not in ``A``.

You can give fixity declarations along with syntax declarations:

..
  ::

  module Second where
    record Σ (A : Set) (B : A → Set) : Set where
      constructor _,_
      field fst : A
            snd : B fst

::


    infix 5 Σ
    syntax Σ A (λ x → B) = [ x ∈ A ] × B

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

Unlike :ref:`mixfix operators <mixfix-operators>` that can be used unapplied
using the name including all the underscores, or partially applied by replacing
only some of the underscores by arguments, syntax must be fully applied.
