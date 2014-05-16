module Term.View where

import           Prelude.Extras                   (Eq1((==#)))
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)

import           Term

data Term abs term v
    = Lam (abs term v)
    | Pi (term v) (abs term v)
    | Equal (term v) (term v) (term v)
    | App (Head v) [Elim term v]
    | Set
    deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Eq1 term, Eq1 (abs term)) => Eq1 (Term abs term) where
    Lam body1 ==# Lam body2 =
        body1 ==# body2
    Pi domain1 codomain1 ==# Pi domain2 codomain2 =
        domain1 ==# domain2 && codomain1 ==# codomain2
    Equal type1 x1 y1 ==# Equal type2 x2 y2 =
        type1 ==# type2 && x1 ==# x2 && y1 ==# y2
    App h1 els1 ==# App h2 els2 =
        h1 == h2 && and (zipWith (==#) els1 els2)
    Set ==# Set =
        True
    _ ==# _ =
        False

var :: v -> Term abs term v
var v = App (Var v) []
