..
  ::
  module tools.search-about where

.. _search-about:

*****************************
Search Definitions in Scope
*****************************

Since version 2.5.1 Agda supports the command ``Search About`` that searches
the objects in scope, looking for definitions matching a set of constraints
given by the user.

Usage
=====

The tool is invoked by choosing ``Search About`` in the goal menu or pressing
``C-c C-z``. It opens a prompt and users can then input a list of space-separated
identifiers and string literals. The search returns the definitions in scope whose
type contains *all* of the mentioned identifiers and whose name contains *all* of
the string literals as substrings.

For instance, in the following module::

  open import Agda.Builtin.Char
  open import Agda.Builtin.Char.Properties
  open import Agda.Builtin.String
  open import Agda.Builtin.String.Properties

running ``Search About`` on ``Char String`` returns:

    Definitions about Char, String
      primShowChar
       : Char → String
      primStringFromList
       : Agda.Builtin.List.List Char → String
      primStringToList
       : String → Agda.Builtin.List.List Char
      primStringToListInjective
       : (a b : String) →
         primStringToList a Agda.Builtin.Equality.≡ primStringToList b →
         a Agda.Builtin.Equality.≡ b

and running ``Search About`` on ``String "Injective"`` returns:

    Definitions about String, "Injective"
      primStringToListInjective
       : (a b : String) →
         primStringToList a Agda.Builtin.Equality.≡ primStringToList b →
         a Agda.Builtin.Equality.≡ b
