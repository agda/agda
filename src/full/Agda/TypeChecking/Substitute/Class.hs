{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Substitute.Class where

import Control.Arrow ((***), second)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute.DeBruijn

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

class DeBruijn (SubstArg a) => Subst a where
  type SubstArg a
  applySubst :: Substitution' (SubstArg a) -> a -> a

  default applySubst :: (a ~ f b, Functor f, Subst b, SubstArg a ~ SubstArg b) => Substitution' (SubstArg a) -> a -> a
  applySubst rho = fmap (applySubst rho)

-- | Simple constraint alias for a `Subst` instance `a` with arg type `t`.
type SubstWith t a = (Subst a, SubstArg a ~ t)

-- | `Subst` instance whose agument type is itself
type EndoSubst a = SubstWith a a

-- | `Subst` instance whose argument type is `Term`
type TermSubst a = SubstWith Term a

-- | Raise de Bruijn index, i.e. weakening
raise :: Subst a => Nat -> a -> a
raise = raiseFrom 0

raiseFrom :: Subst a => Nat -> Nat -> a -> a
raiseFrom n k = applySubst (raiseFromS n k)

-- | Replace de Bruijn index i by a 'Term' in something.
subst :: Subst a => Int -> SubstArg a -> a -> a
subst i u = applySubst $ singletonS i u

strengthen :: Subst a => Impossible -> a -> a
strengthen err = applySubst (strengthenS err 1)

-- | Replace what is now de Bruijn index 0, but go under n binders.
--   @substUnder n u == subst n (raise n u)@.
substUnder :: Subst a => Nat -> SubstArg a -> a -> a
substUnder n u = applySubst (liftS n (singletonS 0 u))

-- ** Identity instances

instance Subst QName where
  type SubstArg QName = Term
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

{-# INLINABLE consS #-}
consS :: DeBruijn a => a -> Substitution' a -> Substitution' a
consS t (Wk m rho)
  | Just n <- deBruijnView t,
    n + 1 == m = wkS (m - 1) (liftS 1 rho)
consS u rho = seq u (u :# rho)
{-# SPECIALIZE consS :: Term  -> Substitution' Term  -> Substitution' Term #-}
{-# SPECIALIZE consS :: Level -> Substitution' Level -> Substitution' Level #-}

{-# INLINABLE singletonS #-}
-- | To replace index @n@ by term @u@, do @applySubst (singletonS n u)@.
--   @
--               Γ, Δ ⊢ u : A
--    ---------------------------------
--    Γ, Δ ⊢ singletonS |Δ| u : Γ, A, Δ
--   @
singletonS :: DeBruijn a => Int -> a -> Substitution' a
singletonS n u = map deBruijnVar [0..n-1] ++# consS u (raiseS n)
  -- ALT: foldl (\ s i -> deBruijnVar i `consS` s) (consS u $ raiseS n) $ downFrom n
{-# SPECIALIZE singletonS :: Int -> Term -> Substitution' Term #-}
{-# SPECIALIZE singletonS :: Int -> Level -> Substitution' Level #-}

-- | Single substitution without disturbing any deBruijn indices.
--   @
--             Γ, A, Δ ⊢ u : A
--    ---------------------------------
--    Γ, A, Δ ⊢ inplace |Δ| u : Γ, A, Δ
--   @
inplaceS :: EndoSubst a => Int -> a -> Substitution' a
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
dropS n (EmptyS err)       = throwImpossible err
dropS n (Lift m rho)
  -- dropS n (Lift m rho) =
  --   wkS 1 $ dropS (n - 1) $ liftS (m - 1) rho
  | n > m     = wkS m $ dropS (n - m) rho
  | otherwise = wkS n $ liftS (m - n) rho
dropS n (Strengthen err m rho)
  | n < m     = Strengthen err (m - n) rho
  | otherwise = dropS (n - m) rho

{-# INLINABLE composeS #-}
-- | @applySubst (ρ `composeS` σ) v == applySubst ρ (applySubst σ v)@
composeS :: EndoSubst a => Substitution' a -> Substitution' a -> Substitution' a
composeS rho IdS = rho
composeS IdS sgm = sgm
composeS rho (EmptyS err) = EmptyS err
composeS rho (Wk n sgm) = composeS (dropS n rho) sgm
composeS rho (u :# sgm) = applySubst rho u :# composeS rho sgm
composeS rho (Strengthen err n sgm) = Strengthen err n (composeS rho sgm)
composeS rho (Lift 0 sgm) = __IMPOSSIBLE__
composeS (u :# rho) (Lift n sgm) = u :# composeS rho (liftS (n - 1) sgm)
composeS rho (Lift n sgm) = lookupS rho 0 :# composeS rho (wkS 1 (liftS (n - 1) sgm))

-- If Γ ⊢ ρ : Δ, Θ then splitS |Θ| ρ = (σ, δ), with
--   Γ ⊢ σ : Δ
--   Γ ⊢ δ : Θσ
splitS :: Int -> Substitution' a -> (Substitution' a, Substitution' a)
splitS 0 rho                    = (rho, EmptyS impossible)
splitS n (u :# rho)             = second (u :#) $ splitS (n - 1) rho
splitS n (Lift 0 _)             = __IMPOSSIBLE__
splitS n (Wk m rho)             = wkS m *** wkS m $ splitS n rho
splitS n IdS                    = ( raiseS n
                                  , liftS n $ EmptyS impossible
                                  )
splitS n (Lift m rho)           = wkS 1 *** liftS 1 $
                                  splitS (n - 1) (liftS (m - 1) rho)
splitS n (EmptyS err)           = __IMPOSSIBLE__
splitS n (Strengthen err m rho)
  -- splitS n (Strengthen err 1 rho) =
  --   second (Strengthen err) $ splitS (n - 1) rho
  | n > m     = second (Strengthen err m) $
                splitS (n - m) rho
  | otherwise = second (Strengthen err n) $
                splitS 0 (Strengthen err (m - n) rho)

infixr 4 ++#

(++#) :: DeBruijn a => [a] -> Substitution' a -> Substitution' a
us ++# rho = foldr consS rho us

-- | @
--      Γ ⊢ ρ : Δ  Γ ⊢ reverse vs : Θ
--      ----------------------------- (treating Nothing as having any type)
--        Γ ⊢ prependS vs ρ : Δ, Θ
--   @
prependS :: DeBruijn a => Impossible -> [Maybe a] -> Substitution' a -> Substitution' a
prependS err us rho = go 0 us
  where
  -- The function strengthenS' is not used here, to avoid replacing
  -- the "error message" of a potential outermost Strengthen
  -- constructor in rho.
  str 0 = id
  str n = Strengthen err n

  go !n (Just u  : us) = str n (consS u (go 0 us))
  go  n (Nothing : us) = go (1 + n) us
  go  n []             = str n rho

-- | @
--        Γ ⊢ reverse vs : Δ
--      -----------------------------
--        Γ ⊢ parallelS vs ρ : Γ, Δ
--   @
--
--   Note the @Γ@ in @Γ, Δ@.
parallelS :: DeBruijn a => [a] -> Substitution' a
parallelS us = us ++# idS

-- | Γ ⊢ (strengthenS ⊥ |Δ|) : Γ,Δ
strengthenS :: Impossible -> Int -> Substitution' a
strengthenS err n = case compare n 0 of
  LT -> __IMPOSSIBLE__
  EQ -> idS
  GT -> Strengthen err n idS

-- | A \"smart\" variant of 'Strengthen'. If 'strengthenS' is applied
-- to a substitution with an outermost 'Strengthen' constructor, then
-- the \"error message\" of that constructor is discarded in favour of
-- the 'Impossible' argument of this function.
strengthenS' :: Impossible -> Int -> Substitution' a -> Substitution' a
strengthenS' err m rho = case compare m 0 of
  LT -> __IMPOSSIBLE__
  EQ -> rho
  GT -> case rho of
    Strengthen _ n rho -> Strengthen err (m + n) rho
    _                  -> Strengthen err m       rho

{-# INLINABLE lookupS #-}
lookupS :: EndoSubst a => Substitution' a -> Nat -> a
lookupS rho i = case rho of
  IdS                    -> deBruijnVar i
  Wk n IdS               -> let j = i + n in
                            if  j < 0 then __IMPOSSIBLE__ else deBruijnVar j
  Wk n rho               -> applySubst (raiseS n) (lookupS rho i)
  u :# rho   | i == 0    -> u
             | i < 0     -> __IMPOSSIBLE__
             | otherwise -> lookupS rho (i - 1)
  Strengthen err n rho
             | i < 0     -> __IMPOSSIBLE__
             | i < n     -> throwImpossible err
             | otherwise -> lookupS rho (i - n)
  Lift n rho | i < n     -> deBruijnVar i
             | otherwise -> raise n $ lookupS rho (i - n)
  EmptyS err             -> throwImpossible err


-- | lookupS (listS [(x0,t0)..(xn,tn)]) xi = ti, assuming x0 < .. < xn.


listS :: EndoSubst a => [(Int,a)] -> Substitution' a
listS ((i,t):ts) = singletonS i t `composeS` listS ts
listS []         = IdS

-- | @Γ, Ξ, Δ ⊢ raiseFromS |Δ| |Ξ| : Γ, Δ@
raiseFromS :: Nat -> Nat -> Substitution' a
raiseFromS n k = liftS n $ raiseS k


---------------------------------------------------------------------------
-- * Functions on abstractions
--   and things we couldn't do before we could define 'absBody'
---------------------------------------------------------------------------

-- | Instantiate an abstraction. Strict in the term.
absApp :: Subst a => Abs a -> SubstArg a -> a
absApp (Abs   _ v) u = subst 0 u v
absApp (NoAbs _ v) _ = v

-- | Instantiate an abstraction. Lazy in the term, which allow it to be
--   __IMPOSSIBLE__ in the case where the variable shouldn't be used but we
--   cannot use 'noabsApp'. Used in Apply.
lazyAbsApp :: Subst a => Abs a -> SubstArg a -> a
lazyAbsApp (Abs   _ v) u = applySubst (u :# IdS) v  -- Note: do not use consS here!
lazyAbsApp (NoAbs _ v) _ = v

-- | Instantiate an abstraction that doesn't use its argument.
noabsApp :: Subst a => Impossible -> Abs a -> a
noabsApp err (Abs   _ v) = strengthen err v
noabsApp _   (NoAbs _ v) = v

absBody :: Subst a => Abs a -> a
absBody (Abs   _ v) = v
absBody (NoAbs _ v) = raise 1 v

mkAbs :: (Subst a, Free a) => ArgName -> a -> Abs a
mkAbs x v | 0 `freeIn` v = Abs x v
          | otherwise    = NoAbs x (raise (-1) v)

reAbs :: (Subst a, Free a) => Abs a -> Abs a
reAbs (NoAbs x v) = NoAbs x v
reAbs (Abs x v)   = mkAbs x v

-- | @underAbs k a b@ applies @k@ to @a@ and the content of
--   abstraction @b@ and puts the abstraction back.
--   @a@ is raised if abstraction was proper such that
--   at point of application of @k@ and the content of @b@
--   are at the same context.
--   Precondition: @a@ and @b@ are at the same context at call time.
underAbs :: Subst a => (a -> b -> b) -> a -> Abs b -> Abs b
underAbs cont a = \case
  Abs   x t -> Abs   x $ cont (raise 1 a) t
  NoAbs x t -> NoAbs x $ cont a t

-- | @underLambdas n k a b@ drops @n@ initial 'Lam's from @b@,
--   performs operation @k@ on @a@ and the body of @b@,
--   and puts the 'Lam's back.  @a@ is raised correctly
--   according to the number of abstractions.
underLambdas :: TermSubst a => Int -> (a -> Term -> Term) -> a -> Term -> Term
underLambdas n cont = loop n where
  loop 0 a = cont a
  loop n a = \case
    Lam h b -> Lam h $ underAbs (loop $ n-1) a b
    _       -> __IMPOSSIBLE__
