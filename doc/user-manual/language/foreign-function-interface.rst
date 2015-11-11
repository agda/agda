.. _foreign-function-interface:

**************************
Foreign Function Interface
**************************

.. note::
   This is a stub.

Haskell FFI
===========

.. note::
   This section currently only applies
   to the GHC backend.

The GHC backend compiles certain Agda built-ins to special Haskell
types. The mapping between Agda built-in types and Haskell types
is as follows:

+---------------+-------------------+
| Agda Built-in | Haskell Type      |
+===============+===================+
| STRING        | Data.Text.Text    |
+---------------+-------------------+
| CHAR          | Char              |
+---------------+-------------------+
| INTEGER       | Integer           |
+---------------+-------------------+
| BOOL          | Boolean           |
+---------------+-------------------+
