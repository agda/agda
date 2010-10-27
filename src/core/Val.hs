module Val where

type Name = String

-- to simplify: only one data type for
-- values/type values/vector of values/values of telescopes

data Val =
    Lam (Val -> Val)
 |  App Head [Val]
 |  Set
 |  Fun Val (Val -> Val)

data Head =
   Gen Int Name Val           -- generic values
 | Const Name Val               -- defined values, implicit or data types, or constructor

mvar :: Head -> Val
mvar h = App h []

mconst :: Name -> Val -> Val
mconst s v = mvar (Const s v)

eqH (Gen n1 _ _) (Gen n2 _ _) = n1 == n2
eqH (Const s1 _) (Const s2 _) = s1 == s2
eqH _ _ = False

typH (Gen _ _ v) = v
typH (Const _ v) = v

-- apps (App h us1) us2 = App h (us1++us2)

apps :: Val -> [Val] -> Val
apps v [] = v
apps (Lam f) (u:us) = apps (f u) us
apps (App h us) vs = App h (us ++ vs)

app :: Val -> Val -> Val
app u1 u2 = apps u1 [u2]

-- itCurry u ((x1:A1,...,xn:An) -> A) F is (x1:A1,...,xn:An) -> F (u x1...xn)
itCurry :: Val -> Val -> (Val -> Val) -> Val
itCurry u (Fun v g) f = Fun v (\ w -> itCurry (app u w) (g w) f)
itCurry u _ f = f u

-- inst ((x1:A1,...,xn:An) -> A) (u1 ... un) is A[u1,...,un]
inst :: Val -> [Val] -> Val
inst w [] = w
inst (Fun _ f) (u:us) = inst (f u) us
