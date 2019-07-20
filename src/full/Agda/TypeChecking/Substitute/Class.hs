
module Agda.TypeChecking.Substitute.Class where

import Control.Arrow ((***), second)


import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute.DeBruijn

import Agda.Utils.Empty
import Agda.Utils.List

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Application
---------------------------------------------------------------------------

-- | Apply something to a bunch of arguments.
--   Preserves blocking tags (application can never resolve blocking).
class Apply t where
  apply  :: t -> Args -> t
  applyE :: t -> Elims -> t

  apply t args = applyE t $ map Apply args
  -- Andreas, 2018-06-18, issue #3136
  -- This default instance should be removed to get more precise
  -- crash locations (raise the IMPOSSIBLE in a more specific place).
  -- applyE t es  = apply  t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
    -- precondition: all @es@ are @Apply@s

-- | Apply to some default arguments.
applys :: Apply t => t -> [Term] -> t
applys t vs = apply t $ map defaultArg vs

-- | Apply to a single default argument.
apply1 :: Apply t => t -> Term -> t
apply1 t u = applys t [ u ]

---------------------------------------------------------------------------
-- * Abstraction
---------------------------------------------------------------------------

-- | @(abstract args v) `apply` args --> v[args]@.
class Abstract t where
  abstract :: Telescope -> t -> t

---------------------------------------------------------------------------
-- * Substitution and shifting\/weakening\/strengthening
---------------------------------------------------------------------------

-- | Apply a substitution.

-- For terms:
--
--  Γ ⊢ ρ : Δ
--  Δ ⊢ t : A
-- -----------
-- Γ ⊢ tρ : Aρ

class DeBruijn t => Subst t a | a -> t where
  applySubst :: Substitution' t -> a -> a

-- | Raise de Bruijn index, i.e. weakening
raise :: Subst t a => Nat -> a -> a
raise = raiseFrom 0

raiseFrom :: Subst t a => Nat -> Nat -> a -> a
raiseFrom n k = applySubst (liftS n $ raiseS k)

-- | Replace de Bruijn index i by a 'Term' in something.
subst :: Subst t a => Int -> t -> a -> a
subst i u = applySubst $ singletonS i u

strengthen :: Subst t a => Empty -> a -> a
strengthen err = applySubst (compactS err [Nothing])

-- | Replace what is now de Bruijn index 0, but go under n binders.
--   @substUnder n u == subst n (raise n u)@.
substUnder :: Subst t a => Nat -> t -> a -> a
substUnder n u = applySubst (liftS n (singletonS 0 u))

-- ** Identity instances

instance Subst Term QName where
  applySubst _ q = q

---------------------------------------------------------------------------
-- * Explicit substitutions
---------------------------------------------------------------------------

-- See Syntax.Internal for the definition.

idS :: Substitution' a
idS = IdS

wkS :: Int -> Substitution' a -> Substitution' a
wkS 0 rho        = rho
wkS n (Wk m rho) = Wk (n + m) rho
wkS n (EmptyS err) = EmptyS err
wkS n rho        = Wk n rho

raiseS :: Int -> Substitution' a
raiseS n = wkS n idS

consS :: DeBruijn a => a -> Substitution' a -> Substitution' a
consS t (Wk m rho)
  | Just n <- deBruijnView t,
    n + 1 == m = wkS (m - 1) (liftS 1 rho)
consS u rho = seq u (u :# rho)

-- | To replace index @n@ by term @u@, do @applySubst (singletonS n u)@.
--   @
--               Γ, Δ ⊢ u : A
--    ---------------------------------
--    Γ, Δ ⊢ singletonS |Δ| u : Γ, A, Δ
--   @
singletonS :: DeBruijn a => Int -> a -> Substitution' a
singletonS n u = map deBruijnVar [0..n-1] ++# consS u (raiseS n)
  -- ALT: foldl (\ s i -> deBruijnVar i `consS` s) (consS u $ raiseS n) $ downFrom n

-- | Single substitution without disturbing any deBruijn indices.
--   @
--             Γ, A, Δ ⊢ u : A
--    ---------------------------------
--    Γ, A, Δ ⊢ inplace |Δ| u : Γ, A, Δ
--   @
inplaceS :: Subst a a => Int -> a -> Substitution' a
inplaceS k u = singletonS k u `composeS` liftS (k + 1) (raiseS 1)

-- | Lift a substitution under k binders.
liftS :: Int -> Substitution' a -> Substitution' a
liftS 0 rho          = rho
liftS k IdS          = IdS
liftS k (Lift n rho) = Lift (n + k) rho
liftS k rho          = Lift k rho

-- | @
--         Γ ⊢ ρ : Δ, Ψ
--      -------------------
--      Γ ⊢ dropS |Ψ| ρ : Δ
--   @
dropS :: Int -> Substitution' a -> Substitution' a
dropS 0 rho                = rho
dropS n IdS                = raiseS n
dropS n (Wk m rho)         = wkS m (dropS n rho)
dropS n (u :# rho)         = dropS (n - 1) rho
dropS n (Strengthen _ rho) = dropS (n - 1) rho
dropS n (Lift 0 rho)       = __IMPOSSIBLE__
dropS n (Lift m rho)       = wkS 1 $ dropS (n - 1) $ liftS (m - 1) rho
dropS n (EmptyS err)       = absurd err

-- | @applySubst (ρ `composeS` σ) v == applySubst ρ (applySubst σ v)@
composeS :: Subst a a => Substitution' a -> Substitution' a -> Substitution' a
composeS rho IdS = rho
composeS IdS sgm = sgm
composeS rho (EmptyS err) = EmptyS err
composeS rho (Wk n sgm) = composeS (dropS n rho) sgm
composeS rho (u :# sgm) = applySubst rho u :# composeS rho sgm
composeS rho (Strengthen err sgm) = Strengthen err (composeS rho sgm)
composeS rho (Lift 0 sgm) = __IMPOSSIBLE__
composeS (u :# rho) (Lift n sgm) = u :# composeS rho (liftS (n - 1) sgm)
composeS rho (Lift n sgm) = lookupS rho 0 :# composeS rho (wkS 1 (liftS (n - 1) sgm))

-- If Γ ⊢ ρ : Δ, Θ then splitS |Θ| ρ = (σ, δ), with
--   Γ ⊢ σ : Δ
--   Γ ⊢ δ : Θσ
splitS :: Int -> Substitution' a -> (Substitution' a, Substitution' a)
splitS 0 rho                  = (rho, EmptyS __IMPOSSIBLE__)
splitS n (u :# rho)           = second (u :#) $ splitS (n - 1) rho
splitS n (Strengthen err rho) = second (Strengthen err) $ splitS (n - 1) rho
splitS n (Lift 0 _)           = __IMPOSSIBLE__
splitS n (Wk m rho)           = wkS m *** wkS m $ splitS n rho
splitS n IdS                  = (raiseS n, liftS n $ EmptyS __IMPOSSIBLE__)
splitS n (Lift m rho)         = wkS 1 *** liftS 1 $ splitS (n - 1) (liftS (m - 1) rho)
splitS n (EmptyS err)         = __IMPOSSIBLE__

infixr 4 ++#

(++#) :: DeBruijn a => [a] -> Substitution' a -> Substitution' a
us ++# rho = foldr consS rho us

-- | @
--      Γ ⊢ ρ : Δ  Γ ⊢ reverse vs : Θ
--      ----------------------------- (treating Nothing as having any type)
--        Γ ⊢ prependS vs ρ : Δ, Θ
--   @
prependS :: DeBruijn a => Empty -> [Maybe a] -> Substitution' a -> Substitution' a
prependS err us rho = foldr f rho us
  where
    f Nothing  rho = Strengthen err rho
    f (Just u) rho = consS u rho

parallelS :: DeBruijn a => [a] -> Substitution' a
parallelS us = us ++# idS

compactS :: DeBruijn a => Empty -> [Maybe a] -> Substitution' a
compactS err us = prependS err us idS

-- | Γ ⊢ (strengthenS ⊥ |Δ|) : Γ,Δ
strengthenS :: Empty -> Int -> Substitution' a
strengthenS err = indexWithDefault __IMPOSSIBLE__ $ iterate (Strengthen err) idS

lookupS :: Subst a a => Substitution' a -> Nat -> a
lookupS rho i = case rho of
  IdS                    -> deBruijnVar i
  Wk n IdS               -> let j = i + n in
                            if  j < 0 then __IMPOSSIBLE__ else deBruijnVar j
  Wk n rho               -> applySubst (raiseS n) (lookupS rho i)
  u :# rho   | i == 0    -> u
             | i < 0     -> __IMPOSSIBLE__
             | otherwise -> lookupS rho (i - 1)
  Strengthen err rho
             | i == 0    -> absurd err
             | i < 0     -> __IMPOSSIBLE__
             | otherwise -> lookupS rho (i - 1)
  Lift n rho | i < n     -> deBruijnVar i
             | otherwise -> raise n $ lookupS rho (i - n)
  EmptyS err             -> absurd err


-- | lookupS (listS [(x0,t0)..(xn,tn)]) xi = ti, assuming x0 < .. < xn.

listS :: Subst a a => [(Int,a)] -> Substitution' a
listS ((i,t):ts) = singletonS i t `composeS` listS ts
listS []         = IdS


---------------------------------------------------------------------------
-- * Functions on abstractions
--   and things we couldn't do before we could define 'absBody'
---------------------------------------------------------------------------

-- | Instantiate an abstraction. Strict in the term.
absApp :: Subst t a => Abs a -> t -> a
absApp (Abs   _ v) u = subst 0 u v
absApp (NoAbs _ v) _ = v

-- | Instantiate an abstraction. Lazy in the term, which allow it to be
--   __IMPOSSIBLE__ in the case where the variable shouldn't be used but we
--   cannot use 'noabsApp'. Used in Apply.
lazyAbsApp :: Subst t a => Abs a -> t -> a
lazyAbsApp (Abs   _ v) u = applySubst (u :# IdS) v  -- Note: do not use consS here!
lazyAbsApp (NoAbs _ v) _ = v

-- | Instantiate an abstraction that doesn't use its argument.
noabsApp :: Subst t a => Empty -> Abs a -> a
noabsApp err (Abs   _ v) = strengthen err v
noabsApp _   (NoAbs _ v) = v

absBody :: Subst t a => Abs a -> a
absBody (Abs   _ v) = v
absBody (NoAbs _ v) = raise 1 v

mkAbs :: (Subst t a, Free a) => ArgName -> a -> Abs a
mkAbs x v | 0 `freeIn` v = Abs x v
          | otherwise    = NoAbs x (raise (-1) v)

reAbs :: (Subst t a, Free a) => Abs a -> Abs a
reAbs (NoAbs x v) = NoAbs x v
reAbs (Abs x v)   = mkAbs x v

-- | @underAbs k a b@ applies @k@ to @a@ and the content of
--   abstraction @b@ and puts the abstraction back.
--   @a@ is raised if abstraction was proper such that
--   at point of application of @k@ and the content of @b@
--   are at the same context.
--   Precondition: @a@ and @b@ are at the same context at call time.
underAbs :: Subst t a => (a -> b -> b) -> a -> Abs b -> Abs b
underAbs cont a b = case b of
  Abs   x t -> Abs   x $ cont (raise 1 a) t
  NoAbs x t -> NoAbs x $ cont a t

-- | @underLambdas n k a b@ drops @n@ initial 'Lam's from @b@,
--   performs operation @k@ on @a@ and the body of @b@,
--   and puts the 'Lam's back.  @a@ is raised correctly
--   according to the number of abstractions.
underLambdas :: Subst Term a => Int -> (a -> Term -> Term) -> a -> Term -> Term
underLambdas n cont a = loop n a where
  loop 0 a v = cont a v
  loop n a v = case v of
    Lam h b -> Lam h $ underAbs (loop $ n-1) a b
    _       -> __IMPOSSIBLE__
