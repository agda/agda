.. _core-language:

*************
Core language
*************

.. note::
   This is a stub

.. code-block:: haskell

  data Term = Var Int Elims
            | Def QName Elims               -- ^ @f es@, possibly a delta/iota-redex
            | Con ConHead Args              -- ^ @c vs@
            | Lam ArgInfo (Abs Term)        -- ^ Terms are beta normal. Relevance is ignored
            | Lit Literal
            | Pi (Dom Type) (Abs Type)      -- ^ dependent or non-dependent function space
            | Sort Sort
            | Level Level
            | MetaV MetaId Elims
            | DontCare Term
              -- ^ Irrelevant stuff in relevant position, but created
              --   in an irrelevant context.

