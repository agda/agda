.. _positivity-checking:

*******************
Positivity Checking
*******************

.. note::
   This is a stub.

.. _no-positivity-check:

NO_POSITIVITY_CHECK pragma
__________________________

The pragma switch off the positivity checker for data/record
definitions and mutual blocks.

The pragma must precede a data/record definition or a mutual block.

The pragma cannot be used in safe mode.

Examples:

* Skipping a single data definition.

  .. code-block:: agda

       {-# NO_POSITIVITY_CHECK #-}
       data D : Set where
         lam : (D → D) → D

* Skipping a single record definition.

  .. code-block:: agda

       {-# NO_POSITIVITY_CHECK #-}
       record U : Set where
         field ap : U → U

* Skipping an old-style mutual block: Somewhere within a mutual block
  before a data/record definition.

  .. code-block:: agda

       mutual
         data D : Set where
           lam : (D → D) → D

         {-# NO_POSITIVITY_CHECK #-}
         record U : Set where
           field ap : U → U

* Skipping an old-style mutual block: Before the ``mutual`` keyword.

  .. code-block:: agda


       {-# NO_POSITIVITY_CHECK #-}
       mutual
         data D : Set where
           lam : (D → D) → D

         record U : Set where
             field ap : U → U

* Skipping a new-style mutual block: Anywhere before the declaration
  and the definition of a data/record in the block.

  .. code-block:: agda

     record U : Set
     {-# NO_POSITIVITY_CHECK #-}
     data D   : Set

     record U where
       field ap : U → U

     {-# NO_POSITIVITY_CHECK #-}
     data D where
       lam : (D → D) → D

