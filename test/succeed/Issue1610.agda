
postulate Name : Set
{-# BUILTIN QNAME Name #-}

data ⊤ : Set where
  tt : ⊤

data Term : Set where
  con : Name → Term → Term

data X : ⊤ → Set where
  x : {t : ⊤} → X t

data Y : Set where
  y : Y


-- this type checks
g : {t : ⊤} → Term → X t
g {t} (con nm args) = x {t}

-- this doesn't
f : {t : ⊤} → Term → X t
f {t} (con (quote Y.y) args) = x {t}
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
-- offending line is above
f t = x

-- t != args of type ⊤
-- when checking that the expression x {t} has type X args
