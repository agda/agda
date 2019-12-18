Release notes for Agda 2 version 2.2.0
======================================

Important changes since 2.1.2 (which was released 2007-08-16):

Language
--------

* Exhaustive pattern checking. Agda complains if there are missing
  clauses in a function definition.

* Coinductive types are supported. This feature is under
  development/evaluation, and may change.

  http://wiki.portal.chalmers.se/agda/agda.php?n=ReferenceManual.Codatatypes

* Another experimental feature: Sized types, which can make it easier
  to explain why your code is terminating.

* Improved constraint solving for functions with constructor headed
  right hand sides.

  http://wiki.portal.chalmers.se/agda/agda.php?n=ReferenceManual.FindingTheValuesOfImplicitArguments

* A simple, well-typed foreign function interface, which allows use of
  Haskell functions in Agda code.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.FFI

* The tokens `forall`, `->` and `\` can be written as `∀`, `→` and
  `λ`.

* Absurd lambdas: `λ ()` and `λ {}`.

  http://thread.gmane.org/gmane.comp.lang.agda/440

* Record fields whose values can be inferred can be omitted.

* Agda complains if it spots an unreachable clause, or if a pattern
  variable "shadows" a hidden constructor of matching type.

  http://thread.gmane.org/gmane.comp.lang.agda/720

Tools
-----

* Case-split: The user interface can replace a pattern variable with
  the corresponding constructor patterns. You get one new left-hand
  side for every possible constructor.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.QuickGuideToEditingTypeCheckingAndCompilingAgdaCode

* The MAlonzo compiler.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.MAlonzo

* A new Emacs input method, which contains bindings for many Unicode
  symbols, is by default activated in the Emacs mode.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.UnicodeInput

* Highlighted, hyperlinked HTML can be generated from Agda source
  code.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.HowToGenerateWebPagesFromSourceCode

* The command-line interactive mode (`agda -I`) is no longer
  supported, but should still work.

  http://thread.gmane.org/gmane.comp.lang.agda/245

* Reload times when working on large projects are now considerably
  better.

  http://thread.gmane.org/gmane.comp.lang.agda/551

Libraries
---------

* A standard library is under development.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary

Documentation
-------------

* The Agda wiki is better organised. It should be easier for a
  newcomer to find relevant information now.

  http://wiki.portal.chalmers.se/agda/

Infrastructure
--------------

* Easy-to-install packages for Windows and Debian/Ubuntu have been
  prepared.

  http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download

* Agda 2.2.0 is available from Hackage.

  http://hackage.haskell.org/
