{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE PatternGuards      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Substitute
  ( module Agda.TypeChecking.Substitute
  , Substitution'(..), Substitution
  ) where

import Control.Arrow ((***), second)

import Data.Function
import Data.Functor
import Data.List hiding (sort, drop)
import qualified Data.List as List
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Data.Typeable (Typeable)

import Debug.Trace (trace)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Free as Free
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Positivity.Occurrence as Occ

import Agda.Utils.Empty
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
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
  applyE t es  = apply  t $ map argFromElim es
    -- precondition: all @es@ are @Apply@s

-- | Apply to a single argument.
apply1 :: Apply t => t -> Term -> t
apply1 t u = apply t [ defaultArg u ]

instance Apply Term where
  applyE m [] = m
  applyE m es =
    case m of
      Var i es'   -> Var i (es' ++ es)
      Def f es'   -> defApp f es' es  -- remove projection redexes
      Con c args  -> conApp c args es
      Lam _ b     ->
        case es of
          Apply a : es0 -> lazyAbsApp b (unArg a) `applyE` es0
          _             -> __IMPOSSIBLE__
      MetaV x es' -> MetaV x (es' ++ es)
      Shared p    -> Shared $ applyE p es
      Lit{}       -> __IMPOSSIBLE__
      Level{}     -> __IMPOSSIBLE__
      Pi _ _      -> __IMPOSSIBLE__
      Sort _      -> __IMPOSSIBLE__
      DontCare mv -> dontCare $ mv `applyE` es  -- Andreas, 2011-10-02
        -- need to go under DontCare, since "with" might resurrect irrelevant term

-- | If $v$ is a record value, @canProject f v@
--   returns its field @f@.
canProject :: QName -> Term -> Maybe (Arg Term)
canProject f v =
  case ignoreSharing v of
    (Con (ConHead _ _ fs) vs) -> do
      i <- elemIndex f fs
      headMaybe (drop i vs)
    _ -> Nothing

-- | Eliminate a constructed term.
conApp :: ConHead -> Args -> Elims -> Term
conApp ch                  args []             = Con ch args
conApp ch                  args (Apply a : es) = conApp ch (args ++ [a]) es
conApp ch@(ConHead c _ fs) args (Proj f  : es) =
  let failure = flip trace __IMPOSSIBLE__ $
        "conApp: constructor " ++ show c ++
        " with fields " ++ show fs ++
        " projected by " ++ show f
      i = maybe failure id            $ elemIndex f fs
      v = maybe failure argToDontCare $ headMaybe $ drop i args
  in  applyE v es
{-
      i = maybe failure id    $ elemIndex f $ map unArg fs
      v = maybe failure unArg $ headMaybe $ drop i args
      -- Andreas, 2013-10-20 see Issue543a:
      -- protect result of irrelevant projection.
      r = maybe __IMPOSSIBLE__ getRelevance $ headMaybe $ drop i fs
      u | Irrelevant <- r = DontCare v
        | otherwise       = v
  in  applyE v es
-}

-- | @defApp f us vs@ applies @Def f us@ to further arguments @vs@,
--   eliminating top projection redexes.
--   If @us@ is not empty, we cannot have a projection redex, since
--   the record argument is the first one.
defApp :: QName -> Elims -> Elims -> Term
defApp f [] (Apply a : es) | Just v <- canProject f (unArg a)
  = argToDontCare v `applyE` es
defApp f es0 es = Def f $ es0 ++ es

-- protect irrelevant fields (see issue 610)
argToDontCare :: Arg Term -> Term
argToDontCare (Arg ai v)
  | Irrelevant <- getRelevance ai     = dontCare v
  | otherwise                         = v

instance Apply Type where
  apply = piApply
  -- Maybe an @applyE@ instance would be useful here as well.
  -- A record type could be applied to a projection name
  -- to yield the field type.
  -- However, this works only in the monad where we can
  -- look up the fields of a record type.

instance Apply Sort where
  applyE s [] = s
  applyE s _  = __IMPOSSIBLE__

instance Apply a => Apply (Ptr a) where
  applyE p xs = fmap (`applyE` xs) p

-- @applyE@ does not make sense for telecopes, definitions, clauses etc.

instance Subst Term a => Apply (Tele a) where
  apply tel               []       = tel
  apply EmptyTel          _        = __IMPOSSIBLE__
  apply (ExtendTel _ tel) (t : ts) = lazyAbsApp tel (unArg t) `apply` ts

instance Apply Definition where
  apply (Defn info x t pol occ df m c inst d) args =
    Defn info x (piApply t args) (apply pol args) (apply occ args) df m c inst (apply d args)

instance Apply RewriteRule where
  apply r args = RewriteRule
    { rewName    = rewName r
    , rewContext = apply (rewContext r) args
    , rewLHS     = applySubst sub (rewLHS r)
    , rewRHS     = applySubst sub (rewRHS r)
    , rewType    = applySubst sub (rewType r)
    }
    where sub = parallelS (map unArg args)

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} Apply [Occ.Occurrence] where
#else
instance Apply [Occ.Occurrence] where
#endif
  apply occ args = List.drop (length args) occ

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} Apply [Polarity] where
#else
instance Apply [Polarity] where
#endif
  apply pol args = List.drop (length args) pol

instance Apply Projection where
  apply p args = p
    { projIndex    = projIndex p - size args
    , projDropPars = projDropPars p `apply` args
    }

instance Apply Defn where
  apply d [] = d
  apply d args = case d of
    Axiom{} -> d
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Nothing } ->
      d { funClauses    = apply cs args
        , funCompiled   = apply cc args
        , funInv        = apply inv args
        }

    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Just p0} ->
      case p0 `apply` args of
        p@Projection{ projIndex = n }
          | n < 0     -> __IMPOSSIBLE__
          -- case: applied only to parameters
          | n > 0     -> d { funProjection = Just p }
          -- case: applied also to record value (n == 0)
          | otherwise ->
              d { funClauses        = apply cs args'
                , funCompiled       = apply cc args'
                , funInv            = apply inv args'
                , funProjection     = if isVar0 then Just p{ projIndex = 0 } else Nothing
                }
              where
                larg  = last args -- the record value
                args' = [larg]
                isVar0 = case ignoreSharing $ unArg larg of Var 0 [] -> True; _ -> False
{-
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Just p@Projection{ projIndex = n } }
        -- case: only applying parameters
      | size args < n -> d { funProjection = Just $ p `apply` args }
        -- case: apply also to record value
      | otherwise     ->
        d { funClauses        = apply cs args'
          , funCompiled       = apply cc args'
          , funInv            = apply inv args'
          , funProjection     = Just $ p { projIndex = 0 } -- Nothing ?
          }
      where args' = [last args]  -- the record value
-}
    Datatype{ dataPars = np, dataSmallPars = sps, dataNonLinPars = nlps, dataClause = cl
            {-, dataArgOccurrences = occ-} } ->
      d { dataPars = np - size args
        , dataSmallPars  = apply sps args
        , dataNonLinPars = apply nlps args
        , dataClause     = apply cl args
--        , dataArgOccurrences = List.drop (length args) occ
        }
    Record{ recPars = np, recConType = t, recClause = cl, recTel = tel
          {-, recArgOccurrences = occ-} } ->
      d { recPars = np - size args, recConType = apply t args
        , recClause = apply cl args, recTel = apply tel args
--        , recArgOccurrences = List.drop (length args) occ
        }
    Constructor{ conPars = np } ->
      d { conPars = np - size args }
    Primitive{ primClauses = cs } ->
      d { primClauses = apply cs args }

instance Apply PrimFun where
    apply (PrimFun x ar def) args   = PrimFun x (ar - size args) $ \vs -> def (args ++ vs)

instance Apply Clause where
    apply (Clause r tel ps b t catchall) args =
      Clause r
             (apply tel args)
             (List.drop (size args) ps)
             (apply b args)
             (applySubst (parallelS (map unArg args)) t)
             catchall

instance Apply CompiledClauses where
  apply cc args = case cc of
    Fail     -> Fail
    Done hs t
      | length hs >= len -> Done (List.drop len hs)
                                 (applySubst
                                    (parallelS $
                                       [ var i | i <- [0..length hs - len - 1]] ++
                                       map unArg args)
                                    t)
      | otherwise -> __IMPOSSIBLE__
    Case n bs
      | n >= len  -> Case (n - len) (apply bs args)
      | otherwise -> __IMPOSSIBLE__
    where
      len = length args

instance Apply a => Apply (WithArity a) where
  apply  (WithArity n a) args = WithArity n $ apply  a args
  applyE (WithArity n a) es   = WithArity n $ applyE a es

instance Apply a => Apply (Case a) where
  apply (Branches cop cs ls m) args =
    Branches cop (apply cs args) (apply ls args) (apply m args)
  applyE (Branches cop cs ls m) es =
    Branches cop (applyE cs es) (applyE ls es) (applyE m es)

instance Apply FunctionInverse where
  apply NotInjective  args = NotInjective
  apply (Inverse inv) args = Inverse $ apply inv args

instance Apply ClauseBody where
  apply  b       []       = b
  apply (Bind b) (a:args) = lazyAbsApp b (unArg a) `apply` args
  apply (Body v) args     = Body $ v `apply` args
  apply  NoBody   _       = NoBody
  applyE  b       []             = b

  applyE (Bind b) (Apply a : es) = lazyAbsApp b (unArg a) `applyE` es
  applyE (Bind b) (Proj{}  : es) = __IMPOSSIBLE__
  applyE (Body v) es             = Body $ v `applyE` es
  applyE  NoBody   _             = NoBody

instance Apply DisplayTerm where
  apply (DTerm v)          args = DTerm $ apply v args
  apply (DDot v)           args = DDot  $ apply v args
  apply (DCon c vs)        args = DCon c $ vs ++ map (fmap DTerm) args
  apply (DDef c es)        args = DDef c $ es ++ map (Apply . fmap DTerm) args
  apply (DWithApp v ws args') args = DWithApp v ws $ args' ++ args

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} Apply t => Apply [t] where
#else
instance Apply t => Apply [t] where
#endif
  apply  ts args = map (`apply` args) ts
  applyE ts es   = map (`applyE` es) ts

instance Apply t => Apply (Blocked t) where
  apply  b args = fmap (`apply` args) b
  applyE b es   = fmap (`applyE` es) b

instance Apply t => Apply (Maybe t) where
  apply  x args = fmap (`apply` args) x
  applyE x es   = fmap (`applyE` es) x

instance Apply v => Apply (Map k v) where
  apply  x args = fmap (`apply` args) x
  applyE x es   = fmap (`applyE` es) x

instance (Apply a, Apply b) => Apply (a,b) where
  apply  (x,y) args = (apply  x args, apply  y args)
  applyE (x,y) es   = (applyE x es  , applyE y es  )

instance (Apply a, Apply b, Apply c) => Apply (a,b,c) where
  apply  (x,y,z) args = (apply  x args, apply  y args, apply  z args)
  applyE (x,y,z) es   = (applyE x es  , applyE y es  , applyE z es  )

instance DoDrop a => Apply (Drop a) where
  apply x args = dropMore (size args) x

instance DoDrop a => Abstract (Drop a) where
  abstract tel x = unDrop (size tel) x

instance Apply Permutation where
  -- The permutation must start with [0..m - 1]
  -- NB: section (- m) not possible (unary minus), hence (flip (-) m)
  apply (Perm n xs) args = Perm (n - m) $ map (flip (-) m) $ genericDrop m xs
    where
      m = size args

instance Abstract Permutation where
  abstract tel (Perm n xs) = Perm (n + m) $ [0..m - 1] ++ map (+ m) xs
    where
      m = size tel

-- | The type must contain the right number of pis without have to perform any
-- reduction.
piApply :: Type -> Args -> Type
piApply t []                      = t
piApply (El _ (Pi  _ b)) (a:args) = lazyAbsApp b (unArg a) `piApply` args
piApply (El s (Shared p)) args    = piApply (El s $ derefPtr p) args
piApply t args                    =
  trace ("piApply t = " ++ show t ++ "\n  args = " ++ show args) __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Abstraction
---------------------------------------------------------------------------

-- | @(abstract args v) `apply` args --> v[args]@.
class Abstract t where
  abstract :: Telescope -> t -> t

instance Abstract Term where
  abstract = teleLam

instance Abstract Type where
  abstract = telePi_

instance Abstract Sort where
  abstract EmptyTel s = s
  abstract _        s = __IMPOSSIBLE__

instance Abstract Telescope where
  EmptyTel           `abstract` tel = tel
  ExtendTel arg xtel `abstract` tel = ExtendTel arg $ xtel <&> (`abstract` tel)

instance Abstract Definition where
  abstract tel (Defn info x t pol occ df m c inst d) =
    Defn info x (abstract tel t) (abstract tel pol) (abstract tel occ) df m c inst (abstract tel d)

-- | @tel ⊢ (Γ ⊢ lhs ↦ rhs : t)@ becomes @tel, Γ ⊢ lhs ↦ rhs : t)@
--   we do not need to change lhs, rhs, and t since they live in Γ.
--   See 'Abstract Clause'.
instance Abstract RewriteRule where
  abstract tel (RewriteRule q gamma lhs rhs t) =
    RewriteRule q (abstract tel gamma) lhs rhs t

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} Abstract [Occ.Occurrence] where
#else
instance Abstract [Occ.Occurrence] where
#endif
  abstract tel []  = []
  abstract tel occ = replicate (size tel) Mixed ++ occ -- TODO: check occurrence

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} Abstract [Polarity] where
#else
instance Abstract [Polarity] where
#endif
  abstract tel []  = []
  abstract tel pol = replicate (size tel) Invariant ++ pol -- TODO: check polarity

instance Abstract Projection where
  abstract tel p = p
    { projIndex    = size tel + projIndex p
    , projDropPars = abstract tel $ projDropPars p
    , projArgInfo  = if projIndex p > 0 then projArgInfo p else
       domInfo $ last $ telToList tel
    }

instance Abstract Defn where
  abstract tel d = case d of
    Axiom{} -> d
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Nothing  } ->
      d { funClauses  = abstract tel cs
        , funCompiled = abstract tel cc
        , funInv      = abstract tel inv
        }
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Just p } ->
      -- Andreas, 2015-05-11 if projection was applied to Var 0
      -- then abstract over last element of tel (the others are params).
      if projIndex p > 0 then d' else
        d' { funClauses  = abstract tel1 cs
           , funCompiled = abstract tel1 cc
           , funInv      = abstract tel1 inv
           }
        where
          d' = d { funProjection = Just $ abstract tel p }
          tel1 = telFromList $ drop (size tel - 1) $ telToList tel

    Datatype{ dataPars = np, dataSmallPars = sps, dataNonLinPars = nlps, dataClause = cl } ->
      d { dataPars       = np + size tel
        , dataSmallPars  = abstract tel sps
        , dataNonLinPars = abstract tel nlps
        , dataClause     = abstract tel cl
        }
    Record{ recPars = np, recConType = t, recClause = cl, recTel = tel' } ->
      d { recPars    = np + size tel
        , recConType = abstract tel t
        , recClause  = abstract tel cl
        , recTel     = abstract tel tel'
        }
    Constructor{ conPars = np } ->
      d { conPars = np + size tel }
    Primitive{ primClauses = cs } ->
      d { primClauses = abstract tel cs }

instance Abstract PrimFun where
    abstract tel (PrimFun x ar def) = PrimFun x (ar + n) $ \ts -> def $ genericDrop n ts
        where n = size tel

instance Abstract Clause where
  abstract tel (Clause r tel' ps b t catchall) =
    Clause r (abstract tel tel')
           (namedTelVars m tel ++ ps) (abstract tel b)
           t -- nothing to do for t, since it lives under the telescope
           catchall
      where m = size tel + size tel'

instance Abstract CompiledClauses where
  abstract tel Fail = Fail
  abstract tel (Done xs t) = Done (map (argFromDom . fmap fst) (telToList tel) ++ xs) t
  abstract tel (Case n bs) =
    Case (n + fromIntegral (size tel)) (abstract tel bs)

instance Abstract a => Abstract (WithArity a) where
  abstract tel (WithArity n a) = WithArity n $ abstract tel a

instance Abstract a => Abstract (Case a) where
  abstract tel (Branches cop cs ls m) =
    Branches cop (abstract tel cs) (abstract tel ls) (abstract tel m)

telVars :: Int -> Telescope -> [Arg DeBruijnPattern]
telVars m = map (fmap namedThing) . (namedTelVars m)

namedTelVars :: Int -> Telescope -> [NamedArg DeBruijnPattern]
namedTelVars m EmptyTel                     = []
namedTelVars m (ExtendTel (Dom info a) tel) =
  Arg info (namedDBVarP (m-1) $ absName tel) :
  namedTelVars (m-1) (unAbs tel)

instance Abstract FunctionInverse where
  abstract tel NotInjective  = NotInjective
  abstract tel (Inverse inv) = Inverse $ abstract tel inv

instance Abstract ClauseBody where
  abstract EmptyTel          b = b
  abstract (ExtendTel _ tel) b = Bind $ fmap (`abstract` b) tel

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} Abstract t => Abstract [t] where
#else
instance Abstract t => Abstract [t] where
#endif
  abstract tel = map (abstract tel)

instance Abstract t => Abstract (Maybe t) where
  abstract tel x = fmap (abstract tel) x

instance Abstract v => Abstract (Map k v) where
  abstract tel m = fmap (abstract tel) m

abstractArgs :: Abstract a => Args -> a -> a
abstractArgs args x = abstract tel x
    where
        tel   = foldr (\(Arg info x) -> ExtendTel (Dom info $ sort Prop) . Abs x)
                      EmptyTel
              $ zipWith (<$) names args
        names = cycle $ map (stringToArgName . (:[])) ['a'..'z']

---------------------------------------------------------------------------
-- * Explicit substitutions
---------------------------------------------------------------------------

class DeBruijn a where
  debruijnVar  :: Int -> a
  debruijnVar = debruijnNamedVar underscore
  debruijnNamedVar :: String -> Int -> a
  debruijnNamedVar _ = debruijnVar
  debruijnView :: a -> Maybe Int

instance DeBruijn Term where
  debruijnVar = var
  debruijnView (Var n []) = Just n
  debruijnView _ = Nothing

-- See Syntax.Internal for the definition.

idS :: Substitution' a
idS = IdS

wkS :: Int -> Substitution' a -> Substitution' a
wkS 0 rho        = rho
wkS n (Wk m rho) = Wk (n + m) rho
wkS n EmptyS     = EmptyS
wkS n rho        = Wk n rho

raiseS :: Int -> Substitution' a
raiseS n = wkS n idS

consS :: DeBruijn a => a -> Substitution' a -> Substitution' a
consS t (Wk m rho)
  | Just n <- debruijnView t,
    n + 1 == m = wkS (m - 1) (liftS 1 rho)
consS u rho = seq u (u :# rho)

-- | To replace index @n@ by term @u@, do @applySubst (singletonS n u)@.
singletonS :: DeBruijn a => Int -> a -> Substitution' a
singletonS n u = map debruijnVar [0..n-1] ++# consS u (raiseS n)
  -- ALT: foldl (\ s i -> debruijnVar i `consS` s) (consS u $ raiseS n) $ downFrom n

-- | Lift a substitution under k binders.
liftS :: Int -> Substitution' a -> Substitution' a
liftS 0 rho          = rho
liftS k IdS          = IdS
liftS k (Lift n rho) = Lift (n + k) rho
liftS k rho          = Lift k rho

dropS :: Int -> Substitution' a -> Substitution' a
dropS 0 rho                = rho
dropS n IdS                = raiseS n
dropS n (Wk m rho)         = wkS m (dropS n rho)
dropS n (u :# rho)         = dropS (n - 1) rho
dropS n (Strengthen _ rho) = dropS (n - 1) rho
dropS n (Lift 0 rho)       = __IMPOSSIBLE__
dropS n (Lift m rho)       = wkS 1 $ dropS (n - 1) $ liftS (m - 1) rho
dropS n EmptyS             = __IMPOSSIBLE__

-- | @applySubst (ρ `composeS` σ) v == applySubst ρ (applySubst σ v)@
composeS :: Subst a a => Substitution' a -> Substitution' a -> Substitution' a
composeS rho IdS = rho
composeS IdS sgm = sgm
composeS rho EmptyS = EmptyS
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
splitS 0 rho                  = (rho, EmptyS)
splitS n (u :# rho)           = second (u :#) $ splitS (n - 1) rho
splitS n (Strengthen err rho) = second (Strengthen err) $ splitS (n - 1) rho
splitS n (Lift 0 _)           = __IMPOSSIBLE__
splitS n (Wk m rho)           = wkS m *** wkS m $ splitS n rho
splitS n IdS                  = (raiseS n, liftS n EmptyS)
splitS n (Lift m rho)         = wkS 1 *** liftS 1 $ splitS (n - 1) (liftS (m - 1) rho)
splitS n EmptyS               = __IMPOSSIBLE__

infixr 4 ++#

(++#) :: DeBruijn a => [a] -> Substitution' a -> Substitution' a
us ++# rho = foldr consS rho us

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
strengthenS err n
  | n < 0     = __IMPOSSIBLE__
  | otherwise = iterate (Strengthen err) idS !! n

lookupS :: Subst a a => Substitution' a -> Nat -> a
lookupS rho i = case rho of
  IdS                    -> debruijnVar i
  Wk n IdS               -> let j = i + n in
                            if  j < 0 then __IMPOSSIBLE__ else debruijnVar j
  Wk n rho               -> applySubst (raiseS n) (lookupS rho i)
  u :# rho   | i == 0    -> u
             | i < 0     -> __IMPOSSIBLE__
             | otherwise -> lookupS rho (i - 1)
  Strengthen err rho
             | i == 0    -> absurd err
             | i < 0     -> __IMPOSSIBLE__
             | otherwise -> lookupS rho (i - 1)
  Lift n rho | i < n     -> debruijnVar i
             | otherwise -> raise n $ lookupS rho (i - n)
  EmptyS                 -> __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Substitution and raising/shifting/weakening
---------------------------------------------------------------------------

-- | Apply a substitution.

-- For terms:
--
--  Γ ⊢ ρ : Δ
--  Δ ⊢ t : σ
-- -----------
-- Γ ⊢ tρ : σρ

class DeBruijn t => Subst t a | a -> t where
  applySubst :: Substitution' t -> a -> a

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

instance Subst a a => Subst a (Substitution' a) where
  applySubst rho sgm = composeS rho sgm

instance Subst Term Term where
  applySubst IdS t = t
  applySubst rho t    = case t of
    Var i es    -> lookupS rho i `applyE` applySubst rho es
    Lam h m     -> Lam h $ applySubst rho m
    Def f es    -> defApp f [] $ applySubst rho es
    Con c vs    -> Con c $ applySubst rho vs
    MetaV x es  -> MetaV x $ applySubst rho es
    Lit l       -> Lit l
    Level l     -> levelTm $ applySubst rho l
    Pi a b      -> uncurry Pi $ applySubst rho (a,b)
    Sort s      -> sortTm $ applySubst rho s
    Shared p    -> Shared $ applySubst rho p
    DontCare mv -> dontCare $ applySubst rho mv

instance Subst t a => Subst t (Ptr a) where
  applySubst rho = fmap (applySubst rho)

instance Subst Term a => Subst Term (Type' a) where
  applySubst rho (El s t) = applySubst rho s `El` applySubst rho t

instance Subst Term Sort where
  applySubst rho s = case s of
    Type n     -> levelSort $ sub n
    Prop       -> Prop
    Inf        -> Inf
    SizeUniv   -> SizeUniv
    DLub s1 s2 -> DLub (sub s1) (sub s2)
    where sub x = applySubst rho x

instance Subst Term Level where
  applySubst rho (Max as) = Max $ applySubst rho as

instance Subst Term PlusLevel where
  applySubst rho l@ClosedLevel{} = l
  applySubst rho (Plus n l) = Plus n $ applySubst rho l

instance Subst Term LevelAtom where
  applySubst rho (MetaLevel m vs)   = MetaLevel m    $ applySubst rho vs
  applySubst rho (BlockedLevel m v) = BlockedLevel m $ applySubst rho v
  applySubst rho (NeutralLevel _ v) = UnreducedLevel $ applySubst rho v
  applySubst rho (UnreducedLevel v) = UnreducedLevel $ applySubst rho v

instance Subst Term Name where
  applySubst rho = id

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} Subst Term String where
#else
instance Subst Term String where
#endif
  applySubst rho = id

instance Subst Term ConPatternInfo where
  applySubst rho (ConPatternInfo mr mt) = ConPatternInfo mr $ applySubst rho mt

instance Subst Term Pattern where
  applySubst rho p = case p of
    ConP c mt ps -> ConP c (applySubst rho mt) $ applySubst rho ps
    DotP t       -> DotP $ applySubst rho t
    VarP s       -> p
    LitP l       -> p
    ProjP _      -> p

instance Subst Term NLPat where
  applySubst rho p = case p of
    PVar id i -> p
    PWild  -> p
    PDef f es -> PDef f $ applySubst rho es
    PLam i u -> PLam i $ applySubst rho u
    PPi a b -> PPi (applySubst rho a) (applySubst rho b)
    PBoundVar i es -> PBoundVar i $ applySubst rho es
    PTerm u -> PTerm $ applySubst rho u

instance Subst Term RewriteRule where
  applySubst rho (RewriteRule q gamma lhs rhs t) =
    RewriteRule q (applySubst rho gamma)
                  (applySubst (liftS n rho) lhs)
                  (applySubst (liftS n rho) rhs)
                  (applySubst (liftS n rho) t)
    where n = size gamma

instance Subst t a => Subst t (Blocked a) where
  applySubst rho b = fmap (applySubst rho) b

instance Subst Term DisplayForm where
  applySubst rho (Display n ps v) =
    Display n (applySubst (liftS 1 rho) ps)
              (applySubst (liftS n rho) v)

instance Subst Term DisplayTerm where
  applySubst rho (DTerm v)        = DTerm $ applySubst rho v
  applySubst rho (DDot v)         = DDot  $ applySubst rho v
  applySubst rho (DCon c vs)      = DCon c $ applySubst rho vs
  applySubst rho (DDef c es)      = DDef c $ applySubst rho es
  applySubst rho (DWithApp v vs ws) = uncurry3 DWithApp $ applySubst rho (v, vs, ws)

instance Subst t a => Subst t (Tele a) where
  applySubst rho  EmptyTel         = EmptyTel
  applySubst rho (ExtendTel t tel) = uncurry ExtendTel $ applySubst rho (t, tel)

instance Subst Term Constraint where
  applySubst rho c = case c of
    ValueCmp cmp a u v       -> ValueCmp cmp (rf a) (rf u) (rf v)
    ElimCmp ps a v e1 e2     -> ElimCmp ps (rf a) (rf v) (rf e1) (rf e2)
    TypeCmp cmp a b          -> TypeCmp cmp (rf a) (rf b)
    TelCmp a b cmp tel1 tel2 -> TelCmp (rf a) (rf b) cmp (rf tel1) (rf tel2)
    SortCmp cmp s1 s2        -> SortCmp cmp (rf s1) (rf s2)
    LevelCmp cmp l1 l2       -> LevelCmp cmp (rf l1) (rf l2)
    Guarded c cs             -> Guarded (rf c) cs
    IsEmpty r a              -> IsEmpty r (rf a)
    CheckSizeLtSat t         -> CheckSizeLtSat (rf t)
    FindInScope m b cands    -> FindInScope m b (rf cands)
    UnBlock{}                -> c
    where
      rf x = applySubst rho x

instance Subst t a => Subst t (Elim' a) where
  applySubst rho e = case e of
    Apply v -> Apply $ applySubst rho v
    Proj{}  -> e

instance Subst t a => Subst t (Abs a) where
  applySubst rho (Abs x a)   = Abs x $ applySubst (liftS 1 rho) a
  applySubst rho (NoAbs x a) = NoAbs x $ applySubst rho a

instance Subst t a => Subst t (Arg a) where
  applySubst rho = fmap (applySubst rho)

instance Subst t a => Subst t (Named name a) where
  applySubst rho = fmap (applySubst rho)

instance Subst t a => Subst t (Dom a) where
  applySubst rho = fmap (applySubst rho)

instance Subst t a => Subst t (Maybe a) where
  applySubst rho = fmap (applySubst rho)

instance Subst t a => Subst t [a] where
  applySubst rho = map (applySubst rho)

instance Subst Term () where
  applySubst _ _ = ()

instance (Subst t a, Subst t b) => Subst t (a, b) where
  applySubst rho (x,y) = (applySubst rho x, applySubst rho y)

instance (Subst t a, Subst t b, Subst t c) => Subst t (a, b, c) where
  applySubst rho (x,y,z) = (applySubst rho x, applySubst rho y, applySubst rho z)

instance (Subst t a, Subst t b, Subst t c, Subst t d) => Subst t (a, b, c, d) where
  applySubst rho (x,y,z,u) = (applySubst rho x, applySubst rho y, applySubst rho z, applySubst rho u)

instance Subst Term ClauseBody where
  applySubst rho (Body t) = Body $ applySubst rho t
  applySubst rho (Bind b) = Bind $ applySubst rho b
  applySubst _   NoBody   = NoBody

instance Subst Term Candidate where
  applySubst rho (Candidate u t eti) = Candidate (applySubst rho u) (applySubst rho t) eti

instance Subst Term EqualityView where
  applySubst rho (OtherType t) = OtherType
    (applySubst rho t)
  applySubst rho (EqualityType s eq l t a b) = EqualityType
    (applySubst rho s)
    eq
    (applySubst rho l)
    (applySubst rho t)
    (applySubst rho a)
    (applySubst rho b)

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

type TelView = TelV Type
data TelV a  = TelV { theTel :: Tele (Dom a), theCore :: a }
  deriving (Typeable, Show, Functor)

deriving instance (Subst t a, Eq  a) => Eq  (TelV a)
deriving instance (Subst t a, Ord a) => Ord (TelV a)

type ListTel' a = [Dom (a, Type)]
type ListTel = ListTel' ArgName

telFromList' :: (a -> ArgName) -> ListTel' a -> Telescope
telFromList' f = foldr extTel EmptyTel
  where
    extTel (Dom info (x, a)) = ExtendTel (Dom info a) . Abs (f x)

telFromList :: ListTel -> Telescope
telFromList = telFromList' id

telToList :: Telescope -> ListTel
telToList EmptyTel            = []
telToList (ExtendTel arg tel) = fmap (absName tel,) arg : telToList (absBody tel)
  -- Andreas, 2013-12-14: This would work also for 'NoAbs',
  -- since 'absBody' raises.

telToArgs :: Telescope -> [Arg ArgName]
telToArgs tel = [ Arg (domInfo d) (fst $ unDom d) | d <- telToList tel ]

-- | Turn a typed binding @(x1 .. xn : A)@ into a telescope.
bindsToTel' :: (Name -> a) -> [Name] -> Dom Type -> ListTel' a
bindsToTel' f []     t = []
bindsToTel' f (x:xs) t = fmap (f x,) t : bindsToTel' f xs (raise 1 t)

bindsToTel :: [Name] -> Dom Type -> ListTel
bindsToTel = bindsToTel' nameToArgName

-- | Turn a typed binding @(x1 .. xn : A)@ into a telescope.
bindsWithHidingToTel' :: (Name -> a) -> [WithHiding Name] -> Dom Type -> ListTel' a
bindsWithHidingToTel' f []                    t = []
bindsWithHidingToTel' f (WithHiding h x : xs) t =
  fmap (f x,) (mapHiding (mappend h) t) : bindsWithHidingToTel' f xs (raise 1 t)

bindsWithHidingToTel :: [WithHiding Name] -> Dom Type -> ListTel
bindsWithHidingToTel = bindsWithHidingToTel' nameToArgName

-- | Takes off all exposed function domains from the given type.
--   This means that it does not reduce to expose @Pi@-types.
telView' :: Type -> TelView
telView' = telView'UpTo (-1)

-- | @telView'UpTo n t@ takes off the first @n@ exposed function types of @t@.
-- Takes off all (exposed ones) if @n < 0@.
telView'UpTo :: Int -> Type -> TelView
telView'UpTo 0 t = TelV EmptyTel t
telView'UpTo n t = case ignoreSharing $ unEl t of
  Pi a b  -> absV a (absName b) $ telView'UpTo (n - 1) (absBody b)
  _       -> TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

-- | @mkPi dom t = telePi (telFromList [dom]) t@
mkPi :: Dom (ArgName, Type) -> Type -> Type
mkPi (Dom info (x, a)) b = el $ Pi (Dom info a) (mkAbs x b)
  where
    el = El $ dLub (getSort a) (Abs x (getSort b)) -- dLub checks x freeIn

mkLam :: Arg ArgName -> Term -> Term
mkLam a v = Lam (argInfo a) (Abs (unArg a) v)

telePi' :: (Abs Type -> Abs Type) -> Telescope -> Type -> Type
telePi' reAbs = telePi where
  telePi EmptyTel          t = t
  telePi (ExtendTel u tel) t = el $ Pi u $ reAbs b
    where
      b  = (`telePi` t) <$> tel
      s1 = getSort u
      s2 = getSort <$> b
      el = El $ dLub s1 s2

-- | Uses free variable analysis to introduce 'noAbs' bindings.
telePi :: Telescope -> Type -> Type
telePi = telePi' reAbs

-- | Everything will be a 'Abs'.
telePi_ :: Telescope -> Type -> Type
telePi_ = telePi' id

{- OLD
-- | Everything will be a pi.
telePi_  EmptyTel        t = t
telePi_ (ExtendTel u tel) t = el $ Pi u b
  where
    el = El (dLub s1 s2)
    b  = fmap (flip telePi_ t) tel
    s1 = getSort $ unDom u
    s2 = fmap getSort b
-}

teleLam :: Telescope -> Term -> Term
teleLam  EmptyTel         t = t
teleLam (ExtendTel u tel) t = Lam (domInfo u) $ flip teleLam t <$> tel

-- | Performs void ('noAbs') abstraction over telescope.
class TeleNoAbs a where
  teleNoAbs :: a -> Term -> Term

instance TeleNoAbs ListTel where
  teleNoAbs tel t = foldr (\ (Dom ai (x, _)) -> Lam ai . NoAbs x) t tel

instance TeleNoAbs Telescope where
  teleNoAbs tel = teleNoAbs $ telToList tel

-- | Dependent least upper bound, to assign a level to expressions
--   like @forall i -> Set i@.
--
--   @dLub s1 \i.s2 = \omega@ if @i@ appears in the rigid variables of @s2@.
dLub :: Sort -> Abs Sort -> Sort
dLub s1 (NoAbs _ s2) = sLub s1 s2
dLub s1 b@(Abs _ s2) = case occurrence 0 s2 of
  Flexible _    -> DLub s1 b
  Irrelevantly  -> DLub s1 b
  NoOccurrence  -> sLub s1 (noabsApp __IMPOSSIBLE__ b)
--  Free.Unused   -> sLub s1 (absApp b __IMPOSSIBLE__) -- triggers Issue784
  Free.Unused   -> DLub s1 b
  StronglyRigid -> Inf
  Unguarded     -> Inf
  WeaklyRigid   -> Inf

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
underLambdas n cont a v = loop n a v where
  loop 0 a v = cont a v
  loop n a v = case ignoreSharing v of
    Lam h b -> Lam h $ underAbs (loop $ n-1) a b
    _       -> __IMPOSSIBLE__

-- | Methods to retrieve the 'clauseBody'.
class GetBody a where
  getBody         :: a -> Maybe Term
  -- ^ Returns the properly raised clause 'Body',
  --   and 'Nothing' if 'NoBody'.
  getBodyUnraised :: a -> Maybe Term
  -- ^ Just grabs the body, without raising the de Bruijn indices.
  --   This is useful if you want to consider the body in context 'clauseTel'.

instance GetBody ClauseBody where
  getBody NoBody   = Nothing
  getBody (Body v) = Just v
  getBody (Bind b) = getBody $ absBody b

  -- Andreas, 2014-08-25:  The following 'optimization' is WRONG,
  -- since it does not respect the order of Abs and NoAbs.
  -- (They do not commute w.r.t. raise!!)
  --
  -- getBody = body 0
  --   where
  --     -- collect all shiftings and do them in the end in one go
  --     body :: Int -> ClauseBody -> Maybe Term
  --     body _ NoBody             = Nothing
  --     body n (Body v)           = Just $ raise n v
  --     body n (Bind (NoAbs _ v)) = body (n + 1) v
  --     body n (Bind (Abs   _ v)) = body n v

  getBodyUnraised NoBody   = Nothing
  getBodyUnraised (Body v) = Just v
  getBodyUnraised (Bind b) = getBodyUnraised $ unAbs b  -- Does not raise!

instance GetBody Clause where
  getBody         = getBody         . clauseBody
  getBodyUnraised = getBodyUnraised . clauseBody

---------------------------------------------------------------------------
-- * Syntactic equality and order
---------------------------------------------------------------------------

deriving instance Eq Substitution
deriving instance Ord Substitution

deriving instance Eq Sort
deriving instance Ord Sort
deriving instance Eq Level
deriving instance Ord Level
deriving instance Eq PlusLevel
deriving instance Ord LevelAtom
deriving instance Eq NotBlocked
deriving instance Ord NotBlocked
deriving instance Eq t => Eq (Blocked t)
deriving instance Ord t => Ord (Blocked t)
deriving instance Eq Candidate

deriving instance (Subst t a, Eq a)  => Eq  (Elim' a)
deriving instance (Subst t a, Ord a) => Ord (Elim' a)
deriving instance (Subst t a, Eq a)  => Eq  (Tele a)
deriving instance (Subst t a, Ord a) => Ord (Tele a)

deriving instance Eq Constraint
deriving instance Eq Section

instance Ord PlusLevel where
  compare ClosedLevel{} Plus{}            = LT
  compare Plus{} ClosedLevel{}            = GT
  compare (ClosedLevel n) (ClosedLevel m) = compare n m
  -- Compare on the atom first. Makes most sense for levelMax.
  compare (Plus n a) (Plus m b)           = compare (a,n) (b,m)

instance Eq LevelAtom where
  (==) = (==) `on` unLevelAtom

-- | Syntactic 'Type' equality, ignores sort annotations.
instance Eq a => Eq (Type' a) where
  (==) = (==) `on` unEl

instance Ord a => Ord (Type' a) where
  compare = compare `on` unEl

-- | Syntactic 'Term' equality, ignores stuff below @DontCare@ and sharing.
instance Eq Term where
  Var x vs   == Var x' vs'   = x == x' && vs == vs'
  Lam h v    == Lam h' v'    = h == h' && v  == v'
  Lit l      == Lit l'       = l == l'
  Def x vs   == Def x' vs'   = x == x' && vs == vs'
  Con x vs   == Con x' vs'   = x == x' && vs == vs'
  Pi a b     == Pi a' b'     = a == a' && b == b'
  Sort s     == Sort s'      = s == s'
  Level l    == Level l'     = l == l'
  MetaV m vs == MetaV m' vs' = m == m' && vs == vs'
  DontCare _ == DontCare _   = True
  Shared p   == Shared q     = p == q || derefPtr p == derefPtr q
  Shared p   == b            = derefPtr p == b
  a          == Shared q     = a == derefPtr q
  _          == _            = False

instance Ord Term where
  Shared a   `compare` Shared x | a == x = EQ
  Shared a   `compare` x          = compare (derefPtr a) x
  a          `compare` Shared x   = compare a (derefPtr x)
  Var a b    `compare` Var x y    = compare (a, b) (x, y)
  Var{}      `compare` _          = LT
  _          `compare` Var{}      = GT
  Def a b    `compare` Def x y    = compare (a, b) (x, y)
  Def{}      `compare` _          = LT
  _          `compare` Def{}      = GT
  Con a b    `compare` Con x y    = compare (a, b) (x, y)
  Con{}      `compare` _          = LT
  _          `compare` Con{}      = GT
  Lit a      `compare` Lit x      = compare a x
  Lit{}      `compare` _          = LT
  _          `compare` Lit{}      = GT
  Lam a b    `compare` Lam x y    = compare (a, b) (x, y)
  Lam{}      `compare` _          = LT
  _          `compare` Lam{}      = GT
  Pi a b     `compare` Pi x y     = compare (a, b) (x, y)
  Pi{}       `compare` _          = LT
  _          `compare` Pi{}       = GT
  Sort a     `compare` Sort x     = compare a x
  Sort{}     `compare` _          = LT
  _          `compare` Sort{}     = GT
  Level a    `compare` Level x    = compare a x
  Level{}    `compare` _          = LT
  _          `compare` Level{}    = GT
  MetaV a b  `compare` MetaV x y  = compare (a, b) (x, y)
  MetaV{}    `compare` _          = LT
  _          `compare` MetaV{}    = GT
  DontCare{} `compare` DontCare{} = EQ

instance (Subst t a, Eq a) => Eq (Abs a) where
  NoAbs _ a == NoAbs _ b = a == b
  Abs   _ a == Abs   _ b = a == b
  a         == b         = absBody a == absBody b

instance (Subst t a, Ord a) => Ord (Abs a) where
  NoAbs _ a `compare` NoAbs _ b = a `compare` b
  Abs   _ a `compare` Abs   _ b = a `compare` b
  a         `compare` b         = absBody a `compare` absBody b

---------------------------------------------------------------------------
-- * Level stuff
---------------------------------------------------------------------------

-- | The ``rule'', if Agda is considered as a functional
--   pure type system (pts).
--
--   TODO: This needs to be properly implemented, requiring
--   refactoring of Agda's handling of levels.
--   Without impredicativity or 'SizeUniv', Agda's pts rule is
--   just the least upper bound, which is total and commutative.
--   The handling of levels relies on this simplification.
pts :: Sort -> Sort -> Sort
pts = sLub

sLub :: Sort -> Sort -> Sort
sLub s Prop = s
sLub Prop s = s
sLub Inf _ = Inf
sLub _ Inf = Inf
sLub SizeUniv s = s         -- one can freely quantify over sizes in any Set
sLub _ SizeUniv = SizeUniv  -- but everything resulting in a size lives in the SizeUniv
sLub (Type (Max as)) (Type (Max bs)) = Type $ levelMax (as ++ bs)
-- sLub (DLub a b) c = DLub (sLub a c) b -- no longer commutative!
sLub (DLub a NoAbs{}) c = __IMPOSSIBLE__
sLub (DLub a (Abs x b)) c = DLub a $ Abs x $ sLub b $ raise 1 c
sLub a (DLub b c) = DLub (sLub a b) c

lvlView :: Term -> Level
lvlView v = case ignoreSharing v of
  Level l       -> l
  Sort (Type l) -> l
  _             -> Max [Plus 0 $ UnreducedLevel v]

levelMax :: [PlusLevel] -> Level
levelMax as0 = Max $ ns ++ List.sort bs
  where
    as = Prelude.concatMap expand as0
    -- ns is empty or a singleton
    ns = case [ n | ClosedLevel n <- as, n > 0 ] of
      []  -> []
      ns  -> [ ClosedLevel n | let n = Prelude.maximum ns, n > greatestB ]
    bs = subsume [ b | b@Plus{} <- as ]
    greatestB | null bs   = 0
              | otherwise = Prelude.maximum [ n | Plus n _ <- bs ]

    expand l@ClosedLevel{} = [l]
    expand (Plus n l) = map (plus n) $ expand0 $ expandAtom l

    expand0 [] = [ClosedLevel 0]
    expand0 as = as

    expandAtom l = case l of
      BlockedLevel _ v -> expandTm v
      NeutralLevel _ v -> expandTm v
      UnreducedLevel v -> expandTm v
      MetaLevel{}      -> [Plus 0 l]
      where
        expandTm v = case ignoreSharing v of
          Level (Max as)       -> as
          Sort (Type (Max as)) -> as
          _                    -> [Plus 0 l]

    plus n (ClosedLevel m) = ClosedLevel (n + m)
    plus n (Plus m l)      = Plus (n + m) l

    subsume (ClosedLevel{} : _) = __IMPOSSIBLE__
    subsume [] = []
    subsume (Plus n a : bs)
      | not $ null ns = subsume bs
      | otherwise     = Plus n a : subsume [ b | b@(Plus _ a') <- bs, a /= a' ]
      where
        ns = [ m | Plus m a'  <- bs, a == a', m > n ]

sortTm :: Sort -> Term
sortTm (Type l) = Sort $ levelSort l
sortTm s        = Sort s

levelSort :: Level -> Sort
levelSort (Max as)
  | List.any (levelIs Inf     ) as = Inf
  | List.any (levelIs SizeUniv) as = SizeUniv
  where
    levelIs s ClosedLevel{}     = False
    levelIs s (Plus _ l)        = atomIs s l
    atomIs s (NeutralLevel _ a) = tmIs s a
    atomIs s (UnreducedLevel a) = tmIs s a
    atomIs s MetaLevel{}        = False
    atomIs s BlockedLevel{}     = False
    tmIs s (Sort s')            = s == s'
    tmIs s (Shared p)           = tmIs s $ derefPtr p
    tmIs s _                    = False
levelSort l =
  case ignoreSharing $ levelTm l of
    Sort s -> s
    _      -> Type l

levelTm :: Level -> Term
levelTm l =
  case l of
    Max [Plus 0 l] -> unLevelAtom l
    _              -> Level l

unLevelAtom :: LevelAtom -> Term
unLevelAtom (MetaLevel x es)   = MetaV x es
unLevelAtom (NeutralLevel _ v) = v
unLevelAtom (UnreducedLevel v) = v
unLevelAtom (BlockedLevel _ v) = v
