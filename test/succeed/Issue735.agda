-- Andreas, 2012-10-30 Sections
-- Reported by guillaume.brunerie, Oct 24 2012
module Issue735 where

import Common.Level
open import Common.Prelude using (Nat; zero; suc)

{- I often want to use something like sections in Coq. I usually use
parametrized modules but this has at least two issues that Coq does
not have:

1) I need to give a name to the module, and there is often no
   meaningful name to be given

2) It exports the module, so I cannot define a module in another file
   with the same name

I guess I can workaround 2) by declaring the module private, but this
will mean that everything will be indented further (again) and I
really want to avoid that.

I think this can easily be fixed by adding a kind of anonymous
modules.  An anonymous module would be declared by naming it `_`, and
the following code

  module _ params where
    declarations

would be translated to:

  private
    module Fresh params where
      declarations

  open Fresh public

where Fresh is a new name. -}

-- Andreas: this translation is not necessary, because Agda
-- has a concept of sections internally (in Abstract syntax).

-- However, the translation and the actual implementation should
-- have the same semantics, except that a name 'Fresh' is never generated.

-- An empty section with no parameters

module _ where

-- A section with a non-hidden parameter

module _ {a} (A : Set a) where

  data List : Set a where
    []  : List
    _∷_ : (x : A) (xs : List) → List

-- A section with all hidden parameters

module _ {a} {A : Set a} where

  _++_ : List → List → List
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)


test : List Nat
test = (2 ∷ []) ++ (3 ∷ [])
