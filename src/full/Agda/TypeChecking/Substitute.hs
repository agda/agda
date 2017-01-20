{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Substitute
  ( module Agda.TypeChecking.Substitute
  , module Agda.TypeChecking.Substitute.Class
  , module Agda.TypeChecking.Substitute.DeBruijn
  , Substitution'(..), Substitution
  ) where

import Control.Applicative
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
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Free as Free
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Positivity.Occurrence as Occ

import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Substitute.DeBruijn

import Agda.Utils.Empty
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.HashMap (HashMap)

#include "undefined.h"
import Agda.Utils.Impossible

instance Apply Term where
  applyE m [] = m
  applyE m es =
    case m of
      Var i es'   -> Var i (es' ++ es)
      Def f es'   -> defApp f es' es  -- remove projection redexes
      Con c ci args -> conApp c ci args es
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
    (Con (ConHead _ _ fs) _ vs) -> do
      i <- elemIndex f fs
      headMaybe (drop i vs)
    _ -> Nothing

-- | Eliminate a constructed term.
conApp :: ConHead -> ConInfo -> Args -> Elims -> Term
conApp ch                  ci args []             = Con ch ci args
conApp ch                  ci args (Apply a : es) = conApp ch ci (args ++ [a]) es
conApp ch@(ConHead c _ fs) ci args (Proj o f : es) =
  let failure = flip trace __IMPOSSIBLE__ $
        "conApp: constructor " ++ show c ++
        " with fields " ++ show fs ++
        " projected by " ++ show f
      i = maybe failure id            $ elemIndex f fs
      v = maybe failure argToDontCare $ headMaybe $ drop i args
  in  applyE v es

  -- -- Andreas, 2016-07-20 futile attempt to magically fix ProjOrigin
  --     fallback = v
  -- in  if not $ null es then applyE v es else
  --     -- If we have no more eliminations, we can return v
  --     if o == ProjSystem then fallback else
  --       -- If the result is a projected term with ProjSystem,
  --       -- we can can restore it to ProjOrigin o.
  --       -- Otherwise, we get unpleasant printing with eta-expanded record metas.
  --     caseMaybe (hasElims v) fallback $ \ (hd, es0) ->
  --       caseMaybe (initLast es0) fallback $ \ (es1, e2) ->
  --         case e2 of
  --           -- We want to replace this ProjSystem by o.
  --           Proj ProjSystem q -> hd (es1 ++ [Proj o q])
  --             -- Andreas, 2016-07-21 for the whole testsuite
  --             -- this case was never triggered!
  --           _ -> fallback

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

-- Andreas, 2016-01-19: In connection with debugging issue #1783,
-- I consider the Apply instance for Type harmful, as piApply is not
-- safe if the type is not sufficiently reduced.
-- (piApply is not in the monad and hence cannot unfold type synonyms).
--
-- Without apply for types, one has to at least use piApply and be
-- aware of doing something which has a precondition
-- (type sufficiently reduced).
--
-- By grepping for piApply, one can quickly get an overview over
-- potentially harmful uses.
--
-- In general, piApplyM is preferable over piApply since it is more robust
-- and fails earlier than piApply, which may only fail at serialization time,
-- when all thunks are forced.

-- REMOVED:
-- instance Apply Type where
--   apply = piApply
--   -- Maybe an @applyE@ instance would be useful here as well.
--   -- A record type could be applied to a projection name
--   -- to yield the field type.
--   -- However, this works only in the monad where we can
--   -- look up the fields of a record type.

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
  apply (Defn info x t pol occ df m c inst copy ma inj d) args =
    Defn info x (piApply t args) (apply pol args) (apply occ args) df m c inst copy ma inj (apply d args)

instance Apply RewriteRule where
  apply r args = RewriteRule
    { rewName    = rewName r
    , rewContext = apply (rewContext r) args
    , rewHead    = rewHead r
    , rewPats    = applySubst sub (rewPats r)
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

-- | Make sure we only drop variable patterns.
#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} Apply [NamedArg (Pattern' a)] where
#else
instance Apply [NamedArg (Pattern' a)] where
#endif
  apply ps args = loop (length args) ps
    where
    loop 0 ps = ps
    loop n [] = __IMPOSSIBLE__
    loop n (p : ps) =
      let recurse = loop (n - 1) ps
      in  case namedArg p of
            VarP{}  -> recurse
            DotP{}  -> __IMPOSSIBLE__
            LitP{}  -> __IMPOSSIBLE__
            ConP{}  -> __IMPOSSIBLE__
            ProjP{} -> __IMPOSSIBLE__

instance Apply Projection where
  apply p args = p
    { projIndex = projIndex p - size args
    , projLams  = projLams p `apply` args
    }

instance Apply ProjLams where
  apply (ProjLams lams) args = ProjLams $ List.drop (length args) lams

instance Apply Defn where
  apply d [] = d
  apply d args = case d of
    Axiom{} -> d
    AbstractDefn -> d
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
    Record{ recPars = np, recClause = cl, recTel = tel
          {-, recArgOccurrences = occ-} } ->
      d { recPars = np - size args
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
    -- This one is a little bit tricksy after the parameter refinement change.
    -- It is assumed that we only apply a clause to "parameters", i.e.
    -- arguments introduced by lambda lifting. The problem is that these aren't
    -- necessarily the first elements of the clause telescope.
    apply cls@(Clause rl rf tel ps b t catchall) args
      | length args > length ps = __IMPOSSIBLE__
      | otherwise =
      Clause rl rf
             tel'
             (applySubst rhoP $ drop (length args) ps)
             (applySubst rho b)
             (applySubst rho t)
             catchall
      where
        -- We have
        --  Γ ⊢ args, for some outer context Γ
        --  Δ ⊢ ps,   where Δ is the clause telescope (tel)
        rargs = map unArg $ reverse args
        rps   = reverse $ take (length args) ps
        n     = size tel

        -- This is the new telescope. Created by substituting the args into the
        -- appropriate places in the old telescope. We know where those are by
        -- looking at the deBruijn indices of the patterns.
        tel' = newTel n tel rps rargs

        -- We then have to create a substitution from the old telescope to the
        -- new telescope that we can apply to dot patterns and the clause body.
        rhoP :: PatternSubstitution
        rhoP = mkSub DotP n rps rargs
        rho  = mkSub id   n rps rargs

        substP :: Nat -> Term -> [NamedArg DeBruijnPattern] -> [NamedArg DeBruijnPattern]
        substP i v = subst i (DotP v)

        -- Building the substitution from the old telescope to the new. The
        -- interesting case is when we have a variable pattern:
        --  We need Δ′ ⊢ ρ : Δ
        --  where Δ′ = newTel Δ (xⁱ : ps) (v : vs)
        --           = newTel Δ[xⁱ:=v] ps[xⁱ:=v'] vs
        --  Note that we need v' = raise (|Δ| - 1) v, to make Γ ⊢ v valid in
        --  ΓΔ[xⁱ:=v].
        --  A recursive call ρ′ = mkSub (substP i v' ps) vs gets us
        --    Δ′ ⊢ ρ′ : Δ[xⁱ:=v]
        --  so we just need Δ[xⁱ:=v] ⊢ σ : Δ and then ρ = ρ′ ∘ σ.
        --  That's achieved by σ = singletonS i v'.
        mkSub :: Subst a a => (Term -> a) -> Nat -> [NamedArg DeBruijnPattern] -> [Term] -> Substitution' a
        mkSub _ _ [] [] = idS
        mkSub tm n (p : ps) (v : vs) =
          case namedArg p of
            VarP (DBPatVar _ i) -> mkSub tm (n - 1) (substP i v' ps) vs `composeS` singletonS i (tm v')
              where v' = raise (n - 1) v
            DotP{}  -> mkSub tm n ps vs
            LitP{}  -> __IMPOSSIBLE__
            ConP{}  -> __IMPOSSIBLE__
            ProjP{} -> __IMPOSSIBLE__
        mkSub _ _ _ _ = __IMPOSSIBLE__

        -- The parameter patterns 'ps' are all variables or dot patterns. If they
        -- are variables they can appear anywhere in the clause telescope. This
        -- function constructs the new telescope with 'vs' substituted for 'ps'.
        -- Example:
        --    tel = (x : A) (y : B) (z : C) (w : D)
        --    ps  = y@3 w@0
        --    vs  = u v
        --    newTel tel ps vs = (x : A) (z : C[u/y])
        newTel n tel [] [] = tel
        newTel n tel (p : ps) (v : vs) =
          case namedArg p of
            VarP (DBPatVar _ i) -> newTel (n - 1) (subTel (size tel - 1 - i) v tel) (substP i (raise (n - 1) v) ps) vs
            DotP{}              -> newTel n tel ps vs
            LitP{}              -> __IMPOSSIBLE__
            ConP{}              -> __IMPOSSIBLE__
            ProjP{}             -> __IMPOSSIBLE__
        newTel _ tel _ _ = __IMPOSSIBLE__

        -- subTel i v (Δ₁ (xᵢ : A) Δ₂) = Δ₁ Δ₂[xᵢ = v]
        subTel i v EmptyTel = __IMPOSSIBLE__
        subTel 0 v (ExtendTel _ tel) = absApp tel v
        subTel i v (ExtendTel a tel) = ExtendTel a $ subTel (i - 1) (raise 1 v) <$> tel

instance Apply CompiledClauses where
  apply cc args = case cc of
    Fail     -> Fail
    Done hs t
      | length hs >= len ->
         let sub = parallelS $ map var [0..length hs - len - 1] ++ map unArg args
         in  Done (List.drop len hs) $ applySubst sub t
      | otherwise -> __IMPOSSIBLE__
    Case n bs
      | unArg n >= len -> Case (n <&> \ m -> m - len) (apply bs args)
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

instance Apply DisplayTerm where
  apply (DTerm v)          args = DTerm $ apply v args
  apply (DDot v)           args = DDot  $ apply v args
  apply (DCon c ci vs)     args = DCon c ci $ vs ++ map (fmap DTerm) args
  apply (DDef c es)        args = DDef c $ es ++ map (Apply . fmap DTerm) args
  apply (DWithApp v ws es) args = DWithApp v ws $ es ++ map Apply args

  applyE (DTerm v)           es = DTerm $ applyE v es
  applyE (DDot v)            es = DDot  $ applyE v es
  applyE (DCon c ci vs)      es = DCon c ci $ vs ++ map (fmap DTerm) ws
    where ws = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
  applyE (DDef c es')        es = DDef c $ es' ++ map (fmap DTerm) es
  applyE (DWithApp v ws es') es = DWithApp v ws $ es' ++ es

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

instance Apply v => Apply (HashMap k v) where
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

-- | @(x:A)->B(x) `piApply` [u] = B(u)@
--
--   Precondition: The type must contain the right number of pis without
--   having to perform any reduction.
--
--   @piApply@ is potentially unsafe, the monadic 'piApplyM' is preferable.
piApply :: Type -> Args -> Type
piApply t []                      = t
piApply (El _ (Pi  _ b)) (a:args) = lazyAbsApp b (unArg a) `piApply` args
piApply (El s (Shared p)) args    = piApply (El s $ derefPtr p) args
piApply t args                    =
  trace ("piApply t = " ++ show t ++ "\n  args = " ++ show args) __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Abstraction
---------------------------------------------------------------------------

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
  abstract tel (Defn info x t pol occ df m c inst copy ma inj d) =
    Defn info x (abstract tel t) (abstract tel pol) (abstract tel occ) df m c inst copy ma inj (abstract tel d)

-- | @tel ⊢ (Γ ⊢ lhs ↦ rhs : t)@ becomes @tel, Γ ⊢ lhs ↦ rhs : t)@
--   we do not need to change lhs, rhs, and t since they live in Γ.
--   See 'Abstract Clause'.
instance Abstract RewriteRule where
  abstract tel (RewriteRule q gamma f ps rhs t) =
    RewriteRule q (abstract tel gamma) f ps rhs t

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
    { projIndex = size tel + projIndex p
    , projLams  = abstract tel $ projLams p
    }

instance Abstract ProjLams where
  abstract tel (ProjLams lams) = ProjLams $
    map (\ (Dom ai (x, _)) -> Arg ai x) (telToList tel) ++ lams

instance Abstract Defn where
  abstract tel d = case d of
    Axiom{} -> d
    AbstractDefn -> d
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
    Record{ recPars = np, recClause = cl, recTel = tel' } ->
      d { recPars    = np + size tel
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
  abstract tel (Clause rl rf tel' ps b t catchall) =
    Clause rl rf (abstract tel tel')
           (namedTelVars m tel ++ ps)
           b
           t -- nothing to do for t, since it lives under the telescope
           catchall
      where m = size tel + size tel'

instance Abstract CompiledClauses where
  abstract tel Fail = Fail
  abstract tel (Done xs t) = Done (map (argFromDom . fmap fst) (telToList tel) ++ xs) t
  abstract tel (Case n bs) =
    Case (n <&> \ i -> i + fromIntegral (size tel)) (abstract tel bs)

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

instance Abstract v => Abstract (HashMap k v) where
  abstract tel m = fmap (abstract tel) m

abstractArgs :: Abstract a => Args -> a -> a
abstractArgs args x = abstract tel x
    where
        tel   = foldr (\(Arg info x) -> ExtendTel (Dom info $ sort Prop) . Abs x)
                      EmptyTel
              $ zipWith (<$) names args
        names = cycle $ map (stringToArgName . (:[])) ['a'..'z']

---------------------------------------------------------------------------
-- * Substitution and raising/shifting/weakening
---------------------------------------------------------------------------

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renaming _ π) : Term Γ -> Term Δ@
renaming :: forall a. DeBruijn a => Empty -> Permutation -> Substitution' a
renaming err p = prependS err gamma $ raiseS $ size p
  where
    gamma :: [Maybe a]
    gamma = inversePermute p (deBruijnVar :: Int -> a)
    -- gamma = safePermute (invertP (-1) p) $ map deBruijnVar [0..]

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renamingR π) : Term Δ -> Term Γ@
renamingR :: DeBruijn a => Permutation -> Substitution' a
renamingR p@(Perm n _) = permute (reverseP p) (map deBruijnVar [0..]) ++# raiseS n

-- | The permutation should permute the corresponding context. (right-to-left list)
renameP :: Subst t a => Empty -> Permutation -> a -> a
renameP err p = applySubst (renaming err p)

instance Subst a a => Subst a (Substitution' a) where
  applySubst rho sgm = composeS rho sgm

instance Subst Term Term where
  applySubst IdS t = t
  applySubst rho t    = case t of
    Var i es    -> lookupS rho i `applyE` applySubst rho es
    Lam h m     -> Lam h $ applySubst rho m
    Def f es    -> defApp f [] $ applySubst rho es
    Con c ci vs -> Con c ci $ applySubst rho vs
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
    ProjP{}      -> p

instance Subst Term NLPat where
  applySubst rho p = case p of
    PVar id i bvs -> p
    PWild  -> p
    PDef f es -> PDef f $ applySubst rho es
    PLam i u -> PLam i $ applySubst rho u
    PPi a b -> PPi (applySubst rho a) (applySubst rho b)
    PBoundVar i es -> PBoundVar i $ applySubst rho es
    PTerm u -> PTerm $ applySubst rho u

instance Subst Term NLPType where
  applySubst rho (NLPType s a) = NLPType (applySubst rho s) (applySubst rho a)

instance Subst Term RewriteRule where
  applySubst rho (RewriteRule q gamma f ps rhs t) =
    RewriteRule q (applySubst rho gamma)
                f (applySubst (liftS n rho) ps)
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
  applySubst rho (DCon c ci vs)   = DCon c ci $ applySubst rho vs
  applySubst rho (DDef c es)      = DDef c $ applySubst rho es
  applySubst rho (DWithApp v vs es) = uncurry3 DWithApp $ applySubst rho (v, vs, es)

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

instance Subst Term ModuleParameters where
  applySubst rho mp = mp { mpSubstitution = applySubst rho $ mpSubstitution mp }

instance Subst Term A.NamedDotPattern where
  applySubst rho (A.NamedDot x v a) = A.NamedDot x (applySubst rho v) (applySubst rho a)

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

instance (Ord k, Subst t a) => Subst t (Map k a) where
  applySubst rho = fmap (applySubst rho)

instance Subst Term () where
  applySubst _ _ = ()

instance (Subst t a, Subst t b) => Subst t (a, b) where
  applySubst rho (x,y) = (applySubst rho x, applySubst rho y)

instance (Subst t a, Subst t b, Subst t c) => Subst t (a, b, c) where
  applySubst rho (x,y,z) = (applySubst rho x, applySubst rho y, applySubst rho z)

instance (Subst t a, Subst t b, Subst t c, Subst t d) => Subst t (a, b, c, d) where
  applySubst rho (x,y,z,u) = (applySubst rho x, applySubst rho y, applySubst rho z, applySubst rho u)

instance Subst Term Candidate where
  applySubst rho (Candidate u t eti ov) = Candidate (applySubst rho u) (applySubst rho t) eti ov

instance Subst Term EqualityView where
  applySubst rho (OtherType t) = OtherType
    (applySubst rho t)
  applySubst rho (EqualityType s eq l t a b) = EqualityType
    (applySubst rho s)
    eq
    (map (applySubst rho) l)
    (applySubst rho t)
    (applySubst rho a)
    (applySubst rho b)

instance DeBruijn DeBruijnPattern where
  debruijnNamedVar n i  = VarP $ DBPatVar n i
  deBruijnView (VarP x) = Just $ dbPatVarIndex x
  deBruijnView _        = Nothing

fromPatternSubstitution :: PatternSubstitution -> Substitution
fromPatternSubstitution = fmap patternToTerm

applyPatSubst :: (Subst Term a) => PatternSubstitution -> a -> a
applyPatSubst = applySubst . fromPatternSubstitution

instance Subst DeBruijnPattern DeBruijnPattern where
  applySubst IdS p = p
  applySubst rho p = case p of
    VarP x       -> useName (dbPatVarName x) $ lookupS rho $ dbPatVarIndex x
    DotP u       -> DotP $ applyPatSubst rho u
    ConP c ci ps -> ConP c ci $ applySubst rho ps
    LitP x       -> p
    ProjP{}      -> p
    where
      useName :: PatVarName -> DeBruijnPattern -> DeBruijnPattern
      useName n (VarP x) | isUnderscore (dbPatVarName x) = debruijnNamedVar n (dbPatVarIndex x)
      useName _ x = x

---------------------------------------------------------------------------
-- * Projections
---------------------------------------------------------------------------

-- | @projDropParsApply proj o args = 'projDropPars' proj o `'apply'` args@
--
--   This function is an optimization, saving us from construction lambdas we
--   immediately remove through application.
projDropParsApply :: Projection -> ProjOrigin -> Args -> Term
projDropParsApply (Projection prop d r _ lams) o args =
  case initLast $ getProjLams lams of
    -- If we have no more abstractions, we must be a record field
    -- (projection applied already to record value).
    Nothing -> if proper then Def d $ map Apply args else __IMPOSSIBLE__
    Just (pars, Arg i y) ->
      let core = if proper then Lam i $ Abs y $ Var 0 [Proj o d]
                           else Lam i $ Abs y $ Def d [Apply $ Var 0 [] <$ r] -- Issue2226: get ArgInfo for principal argument from projFromType
      -- Now drop pars many args
          (pars', args') = dropCommon pars args
      -- We only have to abstract over the parameters that exceed the arguments.
      -- We only have to apply to the arguments that exceed the parameters.
      in List.foldr (\ (Arg ai x) -> Lam ai . NoAbs x) (core `apply` args') pars'
  where proper = isJust prop

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

type TelView = TelV Type
data TelV a  = TelV { theTel :: Tele (Dom a), theCore :: a }
  deriving (Typeable, Show, Functor)

deriving instance (Subst t a, Eq  a) => Eq  (TelV a)
deriving instance (Subst t a, Ord a) => Ord (TelV a)

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

-- | Uses free variable analysis to introduce 'NoAbs' bindings.
telePi :: Telescope -> Type -> Type
telePi = telePi' reAbs

-- | Everything will be an 'Abs'.
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

-- | Abstract over a telescope in a term, producing lambdas.
--   Dumb abstraction: Always produces 'Abs', never 'NoAbs'.
--
--   The implementation is sound because 'Telescope' does not use 'NoAbs'.
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

-- | In compiled clauses, the variables in the clause body are relative to the
--   pattern variables (including dot patterns) instead of the clause telescope.
compiledClauseBody :: Clause -> Maybe Term
compiledClauseBody cl = applySubst (renamingR perm) $ clauseBody cl
  where perm = fromMaybe __IMPOSSIBLE__ $ clausePerm cl

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
  Con x _ vs == Con x' _ vs' = x == x' && vs == vs'
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
  Con a _ b  `compare` Con x _ y  = compare (a, b) (x, y)
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

instance (Subst t a, Eq a)  => Eq  (Elim' a) where
  Apply  a == Apply  b = a == b
  Proj _ x == Proj _ y = x == y
  _ == _ = False

instance (Subst t a, Ord a) => Ord (Elim' a) where
  Apply  a `compare` Apply  b = a `compare` b
  Proj _ x `compare` Proj _ y = x `compare` y
  Apply{}  `compare` Proj{}   = LT
  Proj{}   `compare` Apply{}  = GT

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

-- | Dependent least upper bound, to assign a level to expressions
--   like @forall i -> Set i@.
--
--   @dLub s1 \i.s2 = \omega@ if @i@ appears in the rigid variables of @s2@.
dLub :: Sort -> Abs Sort -> Sort
dLub s1 (NoAbs _ s2) = sLub s1 s2
dLub s1 b@(Abs _ s2) = case occurrence 0 s2 of
  Flexible _    -> DLub s1 b
  -- Andreas, 2017-01-18, issue #2408:
  -- The sort of @.(a : A) → Set (f a)@ in context @f : .A → Level@
  -- is @dLub Set λ a → Set (lsuc (f a))@, but @DLub@s are not serialized.
  -- Alternatives:
  -- 1. -- Irrelevantly -> sLub s1 (absApp b $ DontCare $ Sort Prop)
  --    We cheat here by simplifying the sort to @Set (lsuc (f *))@
  --    where * is a dummy value.  The rationale is that @f * = f a@ (irrelevance!)
  --    and that if we already have a neutral level @f a@
  --    it should not hurt to have @f *@ even if type @A@ is empty.
  --    However: sorts are printed in error messages when sorts do not match.
  --    Also, sorts with a dummy like Prop would be ill-typed.
  -- 2. We keep the DLub, and serialize it.
  --    That's clean and principled, even though DLubs make level solving harder.
  Irrelevantly  -> DLub s1 b
  NoOccurrence  -> sLub s1 (noabsApp __IMPOSSIBLE__ b)
--  Free.Unused   -> sLub s1 (absApp b __IMPOSSIBLE__) -- triggers Issue784
  Free.Unused   -> DLub s1 b
  StronglyRigid -> Inf
  Unguarded     -> Inf
  WeaklyRigid   -> Inf

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
