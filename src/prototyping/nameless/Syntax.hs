
module Syntax where

import Control.Monad

import Stack
import Name

data Term = Free Name
          | Bound Int
          | App Term Term
          | Lam Scope
          | Pi Term Scope
          | Set
  deriving (Show, Eq)

data Scope = Scope { varName :: String, unScope :: Term }
  deriving (Show, Eq)

topName :: Name -> String
topName Empty = "noname"
topName (_ :< (s, _)) = s

abstract :: Name -> Term -> Scope
abstract me e = Scope (topName me) $ letmeB 0 e
  where
    letmeB this (Free you)
      | you == me                    = Bound this
      | otherwise                    = Free you
    letmeB this (Bound that)         = Bound that
    letmeB this (App e1 e2)          = App (letmeB this e1) (letmeB this e2)
    letmeB this (Lam (Scope x e))    = Lam (Scope x $ letmeB (this + 1) e)
    letmeB this (Pi e1 (Scope x e2)) = Pi (letmeB this e1)
                                        (Scope x $ letmeB (this + 1) e2)
    letmeB this Set                  = Set

instantiate :: Term -> Scope -> Term
instantiate what (Scope _ body) = what'sB 0 body
  where
    what'sB this (Bound that)
      | this == that                   = what
      | otherwise                      = Bound that
    what'sB this (Free you)            = Free you
    what'sB this (App e1 e2)           = App (what'sB this e1) (what'sB this e2)
    what'sB this (Lam (Scope x body))  = Lam (Scope x $ what'sB (this + 1) body)
    what'sB this (Pi e (Scope x body)) = Pi (what'sB this e)
                                          (Scope x $ what'sB (this + 1) body)
    what'sB this Set                   = Set

substitute :: Term -> Name -> Term -> Term
substitute image x = instantiate image . abstract x

lam :: Name -> Term -> Term
lam x e = Lam $ abstract x e

infix 3 :<-

data Binding = Name :<- Term

type Telescope = [Binding]
type Context   = Stack Binding

infixr 4 -->, -->>

(-->) :: Binding -> Term -> Term
(x :<- a) --> b = Pi a $ abstract x b

(-->>) :: Context -> Term -> Term
Empty    -->> a = a
cxt :< b -->> a = cxt -->> b --> a

piView :: Monad m => Agency (Term -> m (Binding, Term))
piView me v = case v of
  Pi a b -> return (me :<- a, instantiate (Free me) b)
  _      -> fail "piView: not a Pi"

data PrefixView = PrefixV Context Term

prefixView :: String -> Agency (Term -> PrefixView)
prefixView x me thing = introduce 0 (PrefixV Empty thing) where
  introduce :: Int -> PrefixView -> PrefixView
  introduce i (PrefixV cxt a) =
    case piView (me :< (x, i)) thing of
      Just (bnd, b) -> introduce (i + 1) $ PrefixV (cxt :< bnd) b
      Nothing       -> PrefixV cxt a

-- weaken A (Δ -> B) = Δ -> A -> B
weaken :: Agency (Term -> Term -> Term)
weaken me dom a = doms -->> (me <: "y" :<- dom) --> range
  where
    PrefixV doms range = prefixView "x" me a

infixl 9 $$

($$) :: Term -> [Term] -> Term
v $$ []       = v
v $$ (u : us) = App v u $$ us

data AppView = AppV Term [Term]

appView :: Term -> AppView
appView v = peel v [] where
  peel (App v u) us = peel v (u : us)
  peel v us         = AppV v us
