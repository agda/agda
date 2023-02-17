{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -ddump-to-file #-}

-- | This module contains the definition of hereditary substitution
-- and application operating on internal syntax which is in β-normal
-- form (β including projection reductions).
--
-- Further, it contains auxiliary functions which rely on substitution
-- but not on reduction.

module Agda.TypeChecking.Substitute
  ( module Agda.TypeChecking.Substitute
  , module Agda.TypeChecking.Substitute.Class
  , module Agda.TypeChecking.Substitute.DeBruijn
  , Substitution'(..), Substitution
  ) where

import Control.Arrow (first, second)
import Control.Monad (guard)

import Data.Coerce
import Data.Function (on)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map.Strict as MapS
import Data.Maybe
import Data.HashMap.Strict (HashMap)

import Debug.Trace (trace)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Free as Free
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Positivity.Occurrence as Occ

import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Substitute.DeBruijn

import Agda.Utils.Either
import Agda.Utils.Empty
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Syntax.Common.Pretty
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible


-- | Apply @Elims@ while using the given function to report ill-typed
--   redexes.
--   Recursive calls for @applyE@ and @applySubst@ happen at type @t@ to
--   propagate the same strategy to subtrees.
{-# SPECIALIZE applyTermE :: (Empty -> Term -> Elims -> Term) -> Term -> Elims -> Term #-}
{-# SPECIALIZE applyTermE :: (Empty -> Term -> Elims -> Term) -> BraveTerm -> Elims -> BraveTerm #-}
applyTermE :: forall t. (Coercible Term t, Apply t, EndoSubst t)
           => (Empty -> Term -> Elims -> Term) -> t -> Elims -> t
applyTermE err' m [] = m
applyTermE err' m es = coerce $
    case coerce m of
      Var i es'   -> Var i (es' ++ es)
      Def f es'   -> defApp f es' es  -- remove projection redexes
      Con c ci args -> conApp @t err' c ci args es
      Lam _ b     ->
        case es of
          Apply a : es0      -> lazyAbsApp (coerce b :: Abs t) (coerce $ unArg a) `app` es0
          IApply _ _ a : es0 -> lazyAbsApp (coerce b :: Abs t) (coerce a)         `app` es0
          _                  -> err __IMPOSSIBLE__
      MetaV x es' -> MetaV x (es' ++ es)
      Lit{}       -> err __IMPOSSIBLE__
      Level{}     -> err __IMPOSSIBLE__
      Pi _ _      -> err __IMPOSSIBLE__
      Sort s      -> Sort $ s `applyE` es
      Dummy s es' -> Dummy s (es' ++ es)
      DontCare mv -> dontCare $ mv `app` es  -- Andreas, 2011-10-02
        -- need to go under DontCare, since "with" might resurrect irrelevant term
   where
     app :: Coercible t a => a -> Elims -> Term
     app u es = coerce $ (coerce u :: t) `applyE` es
     err e = err' e (coerce m) es

instance Apply Term where
  applyE = applyTermE absurd

instance Apply BraveTerm where
  applyE = applyTermE (\ _ t es ->  Dummy "applyE" (Apply (defaultArg t) : es))

-- | If @v@ is a record or constructed value, @canProject f v@
--   returns its field @f@.
canProject :: QName -> Term -> Maybe (Arg Term)
canProject f v =
  case v of
    -- Andreas, 2022-06-10, issue #5922: also unfold data projections
    -- (not just record projections).
    (Con (ConHead _ _ _ fs) _ vs) -> do
      (fld, i) <- findWithIndex ((f ==) . unArg) fs
      -- Jesper, 2019-10-17: dont unfold irrelevant projections
      guard $ not $ isIrrelevant fld
      -- Andreas, 2018-06-12, issue #2170
      -- The ArgInfo from the ConHead is more accurate (relevance subtyping!).
      setArgInfo (getArgInfo fld) <.> isApplyElim =<< listToMaybe (drop i vs)
    _ -> Nothing

-- | Eliminate a constructed term.
conApp :: forall t. (Coercible t Term, Apply t) => (Empty -> Term -> Elims -> Term) -> ConHead -> ConInfo -> Elims -> Elims -> Term
conApp fallback ch                    ci args []                  = Con ch ci args
conApp fallback ch                    ci args    (a@Apply{} : es) = conApp @t fallback ch ci (args ++ [a]) es
conApp fallback ch                    ci args   (a@IApply{} : es) = conApp @t fallback ch ci (args ++ [a]) es
conApp fallback ch@(ConHead c _ _ fs) ci args ees@(Proj o f : es) =
  let failure :: forall a. a -> a
      failure err = flip trace err $ concat
        [ "conApp: constructor ", prettyShow c
        , unlines $ " with fields" : map (("  " ++) . prettyShow) fs
        , unlines $ " and args"    : map (("  " ++) . prettyShow) args
        , " projected by ", prettyShow f
        ]
      isApply e = fromMaybe (failure __IMPOSSIBLE__) $ isApplyElim e
      stuck err = fallback err (Con ch ci args) [Proj o f]
      -- Recurse using the instance for 't', see @applyTermE@
      app :: Term -> Elims -> Term
      app v es = coerce $ applyE (coerce v :: t) es
  in
   case findWithIndex ((f ==) . unArg) fs of
     Nothing -> failure $ stuck __IMPOSSIBLE__ `app` es
     Just (fld, i) -> let
      -- Andreas, 2018-06-12, issue #2170
      -- We safe-guard the projected value by DontCare using the ArgInfo stored at the record constructor,
      -- since the ArgInfo in the constructor application might be inaccurate because of subtyping.
      v = maybe (failure $ stuck __IMPOSSIBLE__) (relToDontCare fld . argToDontCare . isApply) $ listToMaybe $ drop i args
      in v `app` es

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
      v = maybe failure unArg $ listToMaybe $ drop i args
      -- Andreas, 2013-10-20 see Issue543a:
      -- protect result of irrelevant projection.
      r = maybe __IMPOSSIBLE__ getRelevance $ listToMaybe $ drop i fs
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
argToDontCare (Arg ai v) = relToDontCare ai v

relToDontCare :: LensRelevance a => a -> Term -> Term
relToDontCare ai v
  | Irrelevant <- getRelevance ai = dontCare v
  | otherwise                     = v

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
  applyE s es = case s of
    MetaS x es' -> MetaS x $ es' ++ es
    DefS  d es' -> DefS  d $ es' ++ es
    _ -> __IMPOSSIBLE__

-- @applyE@ does not make sense for telecopes, definitions, clauses etc.

instance TermSubst a => Apply (Tele a) where
  apply tel               []       = tel
  apply EmptyTel          _        = __IMPOSSIBLE__
  apply (ExtendTel _ tel) (t : ts) = lazyAbsApp tel (unArg t) `apply` ts

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply Definition where
  apply (Defn info x t st pol occ gens gpars df m c inst copy ma nc inj copat blk lang d) args =
    Defn info x (piApply t args) st (apply pol args) (apply occ args) (apply gens args) (drop (length args) gpars) df m c inst copy ma nc inj copat blk lang (apply d args)

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply RewriteRule where
  apply r args =
    let newContext = apply (rewContext r) args
        sub        = liftS (size newContext) $ parallelS $
                       reverse $ map (PTerm . unArg) args
    in RewriteRule
       { rewName    = rewName r
       , rewContext = newContext
       , rewHead    = rewHead r
       , rewPats    = applySubst sub (rewPats r)
       , rewRHS     = applyNLPatSubst sub (rewRHS r)
       , rewType    = applyNLPatSubst sub (rewType r)
       , rewFromClause = rewFromClause r
       }

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance {-# OVERLAPPING #-} Apply [Occ.Occurrence] where
  apply occ args = List.drop (length args) occ
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance {-# OVERLAPPING #-} Apply [Polarity] where
  apply pol args = List.drop (length args) pol
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply NumGeneralizableArgs where
  apply NoGeneralizableArgs       args = NoGeneralizableArgs
  apply (SomeGeneralizableArgs n) args = SomeGeneralizableArgs (n - length args)
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

-- | Make sure we only drop variable patterns.
instance {-# OVERLAPPING #-} Apply [NamedArg (Pattern' a)] where
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
            DefP{}  -> __IMPOSSIBLE__
            ProjP{} -> __IMPOSSIBLE__
            IApplyP{} -> recurse

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply Projection where
  apply p args = p
    { projIndex = projIndex p - size args
    , projLams  = projLams p `apply` args
    }
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply ProjLams where
  apply (ProjLams lams) args = ProjLams $ List.drop (length args) lams
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply Defn where
  apply d [] = d
  apply d args@(arg1:args1) = case d of
    Axiom{} -> d
    DataOrRecSig n -> DataOrRecSig (n - length args)
    GeneralizableVar{} -> d
    AbstractDefn d -> AbstractDefn $ apply d args
    Function{ funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv
            , funExtLam = extLam
            , funProjection = Left _ } ->
      d { funClauses    = apply cs args
        , funCompiled   = apply cc args
        , funCovering   = apply cov args
        , funInv        = apply inv args
        , funExtLam     = modifySystem (`apply` args) <$> extLam
        }

    Function{ funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv
            , funExtLam = extLam
            , funProjection = Right p0 } ->
      case p0 `apply` args of
        p@Projection{ projIndex = n }
          | n < 0     -> d { funProjection = __IMPOSSIBLE__ } -- TODO (#3123): we actually get here!
          -- case: applied only to parameters
          | n > 0     -> d { funProjection = Right p }
          -- case: applied also to record value (n == 0)
          | otherwise ->
              d { funClauses        = apply cs args'
                , funCompiled       = apply cc args'
                , funCovering       = apply cov args'
                , funInv            = apply inv args'
                , funProjection     = if isVar0 then Right p{ projIndex = 0 } else Left MaybeProjection
                , funExtLam         = modifySystem (\ _ -> __IMPOSSIBLE__) <$> extLam
                }
              where
                larg  = last1 arg1 args1 -- the record value
                args' = [larg]
                isVar0 = case unArg larg of Var 0 [] -> True; _ -> False

    Datatype{ dataPars = np, dataClause = cl } ->
      d { dataPars = np - size args
        , dataClause     = apply cl args
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
    PrimitiveSort{} -> d

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply PrimFun where
  apply (PrimFun x ar occs def) args =
    PrimFun x (ar - n) (drop n occs) $ \ vs -> def (args ++ vs)
    where
    n = size args
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply Clause where
    -- This one is a little bit tricksy after the parameter refinement change.
    -- It is assumed that we only apply a clause to "parameters", i.e.
    -- arguments introduced by lambda lifting. The problem is that these aren't
    -- necessarily the first elements of the clause telescope.
    apply cls@(Clause rl rf tel ps b t catchall exact recursive unreachable ell wm) args
      | length args > length ps = __IMPOSSIBLE__
      | otherwise =
      Clause rl rf
             tel'
             (applySubst rhoP $ drop (length args) ps)
             (applySubst rho b)
             (applySubst rho t)
             catchall
             exact
             recursive
             unreachable
             ell
             wm
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
        rhoP = mkSub dotP n rps rargs
        rho  = mkSub id   n rps rargs

        substP :: Nat -> Term -> [NamedArg DeBruijnPattern] -> [NamedArg DeBruijnPattern]
        substP i v = subst i (dotP v)

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
        mkSub :: EndoSubst a => (Term -> a) -> Nat -> [NamedArg DeBruijnPattern] -> [Term] -> Substitution' a
        mkSub _ _ [] [] = idS
        mkSub tm n (p : ps) (v : vs) =
          case namedArg p of
            VarP _ (DBPatVar _ i) -> mkSub tm (n - 1) (substP i v' ps) vs `composeS` singletonS i (tm v')
              where v' = raise (n - 1) v
            DotP{}  -> mkSub tm n ps vs
            ConP c _ ps' -> mkSub tm n (ps' ++ ps) (projections c v ++ vs)
            DefP{}  -> __IMPOSSIBLE__
            LitP{}  -> __IMPOSSIBLE__
            ProjP{} -> __IMPOSSIBLE__
            IApplyP _ _ _ (DBPatVar _ i) -> mkSub tm (n - 1) (substP i v' ps) vs `composeS` singletonS i (tm v')
              where v' = raise (n - 1) v
        mkSub _ _ _ _ = __IMPOSSIBLE__

        -- The parameter patterns 'ps' are all variables or dot patterns, or eta
        -- expanded record patterns (issue #2550). If they are variables they
        -- can appear anywhere in the clause telescope. This function
        -- constructs the new telescope with 'vs' substituted for 'ps'.
        -- Example:
        --    tel = (x : A) (y : B) (z : C) (w : D)
        --    ps  = y@3 w@0
        --    vs  = u v
        --    newTel tel ps vs = (x : A) (z : C[u/y])
        newTel :: Nat -> Telescope -> [NamedArg DeBruijnPattern] -> [Term] -> Telescope
        newTel n tel [] [] = tel
        newTel n tel (p : ps) (v : vs) =
          case namedArg p of
            VarP _ (DBPatVar _ i) -> newTel (n - 1) (subTel (size tel - 1 - i) v tel) (substP i (raise (n - 1) v) ps) vs
            DotP{}              -> newTel n tel ps vs
            ConP c _ ps'        -> newTel n tel (ps' ++ ps) (projections c v ++ vs)
            DefP{}  -> __IMPOSSIBLE__
            LitP{}  -> __IMPOSSIBLE__
            ProjP{} -> __IMPOSSIBLE__
            IApplyP _ _ _ (DBPatVar _ i) -> newTel (n - 1) (subTel (size tel - 1 - i) v tel) (substP i (raise (n - 1) v) ps) vs
        newTel _ tel _ _ = __IMPOSSIBLE__

        projections :: ConHead -> Term -> [Term]
        projections c v = [ relToDontCare ai $
                            -- #4528: We might have bogus terms here when printing a clause that
                            --        cannot be taken. To mitigate the problem we use a Def instead
                            --        a Proj elim for data constructors, which at least stops conApp
                            --        from crashing. See #4989 for not printing bogus terms at all.
                            case conDataRecord c of
                              IsData     -> defApp f [] [Apply (Arg ai v)]
                                              -- Andreas, 2022-06-10, issue #5922.
                                              -- This was @Def f [Apply (Arg ai v)]@, but are we sure
                                              -- that @v@ isn't a matching @Con@?  The testcase for
                                              -- #5922 does not require this precaution,
                                              -- but I sleep better this way...
                              IsRecord{} -> applyE v [Proj ProjSystem f]
                          | Arg ai f <- conFields c ]

        -- subTel i v (Δ₁ (xᵢ : A) Δ₂) = Δ₁ Δ₂[xᵢ = v]
        subTel i v EmptyTel = __IMPOSSIBLE__
        subTel 0 v (ExtendTel _ tel) = absApp tel v
        subTel i v (ExtendTel a tel) = ExtendTel a $ subTel (i - 1) (raise 1 v) <$> tel

    applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply CompiledClauses where
  apply cc args = case cc of
    Fail hs -> Fail (drop len hs)
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
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply ExtLamInfo where
  apply (ExtLamInfo m b sys) args = ExtLamInfo m b (apply sys args)
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply System where
  -- We assume we apply a system only to arguments introduced by
  -- lambda lifting.
  apply (System tel sys) args
      = if nargs > ntel then __IMPOSSIBLE__
        else System newTel (map (map (f -*- id) -*- f) sys)

    where
      f = applySubst sigma
      nargs = length args
      ntel = size tel
      newTel = apply tel args
      -- newTel ⊢ σ : tel
      sigma = liftS (ntel - nargs) (parallelS (reverse $ map unArg args))

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply a => Apply (WithArity a) where
  apply  (WithArity n a) args = WithArity n $ apply  a args
  applyE (WithArity n a) es   = WithArity n $ applyE a es

instance Apply a => Apply (Case a) where
  apply (Branches cop cs eta ls m b lz) args =
    Branches cop (apply cs args) (second (`apply` args) <$> eta) (apply ls args) (apply m args) b lz
  applyE (Branches cop cs eta ls m b lz) es =
    Branches cop (applyE cs es) (second (`applyE` es) <$> eta)(applyE ls es) (applyE m es) b lz

instance Apply FunctionInverse where
  apply NotInjective  args = NotInjective
  apply (Inverse inv) args = Inverse $ apply inv args

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance Apply DisplayTerm where
  apply (DTerm' v es)      args = DTerm' v       $ es ++ map Apply args
  apply (DDot' v es)       args = DDot' v        $ es ++ map Apply args
  apply (DCon c ci vs)     args = DCon c ci     $ vs ++ map (fmap DTerm) args
  apply (DDef c es)        args = DDef c        $ es ++ map (Apply . fmap DTerm) args
  apply (DWithApp v ws es) args = DWithApp v ws $ es ++ map Apply args

  applyE (DTerm' v es')      es = DTerm' v $ es' ++ es
  applyE (DDot' v es')       es = DDot' v $ es' ++ es
  applyE (DCon c ci vs)      es = DCon c ci $ vs ++ map (fmap DTerm) ws
    where ws = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
  applyE (DDef c es')        es = DDef c $ es' ++ map (fmap DTerm) es
  applyE (DWithApp v ws es') es = DWithApp v ws $ es' ++ es

instance {-# OVERLAPPABLE #-} Apply t => Apply [t] where
  apply  ts args = map (`apply` args) ts
  applyE ts es   = map (`applyE` es) ts

instance Apply t => Apply (Blocked t) where
  apply  b args = fmap (`apply` args) b
  applyE b es   = fmap (`applyE` es) b

instance Apply t => Apply (Maybe t) where
  apply  x args = fmap (`apply` args) x
  applyE x es   = fmap (`applyE` es) x

instance Apply t => Apply (Strict.Maybe t) where
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
  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

instance DoDrop a => Abstract (Drop a) where
  abstract tel x = unDrop (size tel) x

instance Apply Permutation where
  -- The permutation must start with [0..m - 1]
  -- NB: section (- m) not possible (unary minus), hence (flip (-) m)
  apply (Perm n xs) args = Perm (n - m) $ map (flip (-) m) $ drop m xs
    where
      m = size args

  applyE t es = apply t $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

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
piApply t args                    =
  trace ("piApply t = " ++ prettyShow t ++ "\n  args = " ++ prettyShow args) __IMPOSSIBLE__

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
  abstract tel (Defn info x t st pol occ gens gpars df m c inst copy ma nc inj copat blk lang d) =
    Defn info x (abstract tel t) st (abstract tel pol) (abstract tel occ) (abstract tel gens)
      (replicate (size tel) Nothing ++ gpars)
      df m c inst copy ma nc inj copat blk lang (abstract tel d)

-- | @tel ⊢ (Γ ⊢ lhs ↦ rhs : t)@ becomes @tel, Γ ⊢ lhs ↦ rhs : t)@
--   we do not need to change lhs, rhs, and t since they live in Γ.
--   See 'Abstract Clause'.
instance Abstract RewriteRule where
  abstract tel (RewriteRule q gamma f ps rhs t c) =
    RewriteRule q (abstract tel gamma) f ps rhs t c

instance {-# OVERLAPPING #-} Abstract [Occ.Occurrence] where
  abstract tel []  = []
  abstract tel occ = replicate (size tel) Mixed ++ occ -- TODO: check occurrence

instance {-# OVERLAPPING #-} Abstract [Polarity] where
  abstract tel []  = []
  abstract tel pol = replicate (size tel) Invariant ++ pol -- TODO: check polarity

instance Abstract NumGeneralizableArgs where
  abstract tel NoGeneralizableArgs       = NoGeneralizableArgs
  abstract tel (SomeGeneralizableArgs n) = SomeGeneralizableArgs (size tel + n)

instance Abstract Projection where
  abstract tel p = p
    { projIndex = size tel + projIndex p
    , projLams  = abstract tel $ projLams p
    }

instance Abstract ProjLams where
  abstract tel (ProjLams lams) = ProjLams $
    map (\ !dom -> argFromDom (fst <$> dom)) (telToList tel) ++ lams

instance Abstract System where
  abstract tel (System tel1 sys) = System (abstract tel tel1) sys

instance Abstract Defn where
  abstract tel d = case d of
    Axiom{} -> d
    DataOrRecSig n -> DataOrRecSig (size tel + n)
    GeneralizableVar{} -> d
    AbstractDefn d -> AbstractDefn $ abstract tel d
    Function{ funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv
            , funExtLam = extLam
            , funProjection = Left _  } ->
      d { funClauses  = abstract tel cs
        , funCompiled = abstract tel cc
        , funCovering = abstract tel cov
        , funInv      = abstract tel inv
        , funExtLam   = modifySystem (abstract tel) <$> extLam
        }
    Function{ funClauses = cs, funCompiled = cc, funCovering = cov, funInv = inv
            , funExtLam = extLam
            , funProjection = Right p } ->
      -- Andreas, 2015-05-11 if projection was applied to Var 0
      -- then abstract over last element of tel (the others are params).
      if projIndex p > 0 then
        d { funProjection = Right $ abstract tel p
          , funClauses    = map (abstractClause EmptyTel) cs
          }
      else
        d { funProjection = Right $ abstract tel p
          , funClauses    = map (abstractClause tel1) cs
          , funCompiled   = abstract tel1 cc
          , funCovering   = abstract tel1 cov
          , funInv        = abstract tel1 inv
          , funExtLam     = modifySystem (\ _ -> __IMPOSSIBLE__) <$> extLam
          }
        where
          tel1 = telFromList $ drop (size tel - 1) $ telToList tel
          -- #5128: clause telescopes should be abstracted over the full telescope, regardless of
          --        projection shenanigans.
          abstractClause tel1 c = (abstract tel1 c) { clauseTel = abstract tel $ clauseTel c }

    Datatype{ dataPars = np, dataClause = cl } ->
      d { dataPars       = np + size tel
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
    PrimitiveSort{} -> d

instance Abstract PrimFun where
    abstract tel (PrimFun x ar occs def) =
      PrimFun x (ar + n) (replicate n Mixed ++ occs) $ \ts ->
        def $ drop n ts
        where n = size tel

instance Abstract Clause where
  abstract tel (Clause rl rf tel' ps b t catchall exact recursive unreachable ell wm) =
    Clause rl rf (abstract tel tel')
           (namedTelVars m tel ++ ps)
           b
           t -- nothing to do for t, since it lives under the telescope
           catchall
           exact
           recursive
           unreachable
           ell
           wm
      where m = size tel + size tel'

instance Abstract CompiledClauses where
  abstract tel cc = case cc of
      Fail xs   -> Fail (hs ++ xs)
      Done xs t -> Done (hs ++ xs) t
      Case n bs -> Case (n <&> \ i -> i + size tel) (abstract tel bs)
    where
      hs = map (argFromDom . fmap fst) $ telToList tel

instance Abstract a => Abstract (WithArity a) where
  abstract tel (WithArity n a) = WithArity n $ abstract tel a

instance Abstract a => Abstract (Case a) where
  abstract tel (Branches cop cs eta ls m b lz) =
    Branches cop (abstract tel cs) (second (abstract tel) <$> eta)
                 (abstract tel ls) (abstract tel m) b lz

telVars :: Int -> Telescope -> [Arg DeBruijnPattern]
telVars m = map (fmap namedThing) . (namedTelVars m)

namedTelVars :: Int -> Telescope -> [NamedArg DeBruijnPattern]
namedTelVars m EmptyTel                     = []
namedTelVars m (ExtendTel !dom tel) =
  Arg (domInfo dom) (namedDBVarP (m-1) $ absName tel) :
  namedTelVars (m-1) (unAbs tel)

instance Abstract FunctionInverse where
  abstract tel NotInjective  = NotInjective
  abstract tel (Inverse inv) = Inverse $ abstract tel inv

instance {-# OVERLAPPABLE #-} Abstract t => Abstract [t] where
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
        tel   = foldr (\arg@(Arg info x) -> ExtendTel (__DUMMY_TYPE__ <$ domFromArg arg) . Abs x)
                      EmptyTel
              $ zipWith (<$) names args
        names = cycle $ map (stringToArgName . (:[])) ['a'..'z']

---------------------------------------------------------------------------
-- * Substitution and shifting\/weakening\/strengthening
---------------------------------------------------------------------------

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renaming _ π) : Term Γ -> Term Δ@
renaming :: forall a. DeBruijn a => Impossible -> Permutation -> Substitution' a
renaming err p = prependS err gamma $ raiseS $ size p
  where
    gamma :: [Maybe a]
    gamma = inversePermute p (deBruijnVar :: Int -> a)
    -- gamma = safePermute (invertP (-1) p) $ map deBruijnVar [0..]

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renamingR π) : Term Δ -> Term Γ@
renamingR :: DeBruijn a => Permutation -> Substitution' a
renamingR p@(Perm n is) = xs ++# raiseS n
  where
  xs = map (\i -> deBruijnVar (n - 1 - i)) (reverse is)

  -- The list xs used to be defined in the following way:
  --
  --   permute (reverseP p) (map deBruijnVar [0..])
  --
  -- We have that
  --
  --     permute (reverseP p) (map deBruijnVar [0..])
  --   = permute (Perm n $ map ((n - 1) -) $ reverse is)
  --       (map deBruijnVar [0..])
  --   = map (map deBruijnVar [0..] !!)
  --       (map ((n - 1) -) $ reverse is)
  --   = map deBruijnVar (map ((n - 1) -) $ reverse is)
  --   = map (\i -> deBruijnVar (n - 1 - i)) (reverse is).
  --
  -- The latter code is linear in the length of is (if deBruijnVar
  -- takes constant time), while the time complexity of the former
  -- code depends on the value of the largest index in is.

-- | The permutation should permute the corresponding context. (right-to-left list)
renameP :: Subst a => Impossible -> Permutation -> a -> a
renameP err p = applySubst (renaming err p)

instance EndoSubst a => Subst (Substitution' a) where
  type SubstArg (Substitution' a) = a
  applySubst rho sgm = composeS rho sgm

{-# SPECIALIZE applySubstTerm :: Substitution -> Term -> Term #-}
{-# SPECIALIZE applySubstTerm :: Substitution' BraveTerm -> BraveTerm -> BraveTerm #-}
applySubstTerm :: forall t. (Coercible t Term, EndoSubst t, Apply t) => Substitution' t -> t -> t
applySubstTerm IdS t = t
applySubstTerm rho t    = coerce $ case coerce t of
    Var i es    -> coerce $ lookupS rho i  `applyE` subE es
    Lam h m     -> Lam h $ sub @(Abs t) m
    Def f es    -> defApp f [] $ subE es
    Con c ci vs -> Con c ci $ subE vs
    MetaV x es  -> MetaV x $ subE es
    Lit l       -> Lit l
    Level l     -> levelTm $ sub @(Level' t) l
    Pi a b      -> uncurry Pi $ subPi (a,b)
    Sort s      -> Sort $ sub @(Sort' t) s
    DontCare mv -> dontCare $ sub @t mv
    Dummy s es  -> Dummy s $ subE es
 where
   sub :: forall a b. (Coercible b a, SubstWith t a) => b -> b
   sub t = coerce $ applySubst rho (coerce t :: a)
   subE :: Elims -> Elims
   subE  = sub @[Elim' t]
   subPi :: (Dom Type, Abs Type) -> (Dom Type, Abs Type)
   subPi = sub @(Dom' t (Type'' t t), Abs (Type'' t t))

instance Subst Term where
  type SubstArg Term = Term
  applySubst = applySubstTerm

-- András 2023-09-25: we can only put this here, because at the original definition site there's no Subst Term instance.
{-# SPECIALIZE lookupS :: Substitution' Term -> Nat -> Term #-}

instance Subst BraveTerm where
  type SubstArg BraveTerm = BraveTerm
  applySubst = applySubstTerm

instance (Coercible a Term, Subst a, Subst b, SubstArg a ~ SubstArg b) => Subst (Type'' a b) where
  type SubstArg (Type'' a b) = SubstArg a
  applySubst rho (El s t) = applySubst rho s `El` applySubst rho t

instance (Coercible a Term, Subst a) => Subst (Sort' a) where
  type SubstArg (Sort' a) = SubstArg a
  applySubst rho = \case
    Univ u n   -> Univ u $ sub n
    Inf u n    -> Inf u n
    SizeUniv   -> SizeUniv
    LockUniv   -> LockUniv
    LevelUniv  -> LevelUniv
    IntervalUniv -> IntervalUniv
    PiSort a s1 s2 -> coerce $ piSort (coerce $ sub a) (coerce $ sub s1) (coerce $ sub s2)
    FunSort s1 s2 -> coerce $ funSort (coerce $ sub s1) (coerce $ sub s2)
    UnivSort s -> coerce $ univSort $ coerce $ sub s
    MetaS x es -> MetaS x $ sub es
    DefS d es  -> DefS d $ sub es
    s@DummyS{} -> s
    where
      sub :: forall b. (Subst b, SubstArg a ~ SubstArg b) => b -> b
      sub x = applySubst rho x

instance Subst a => Subst (Level' a) where
  type SubstArg (Level' a) = SubstArg a
  applySubst rho (Max n as) = Max n $ applySubst rho as

instance Subst a => Subst (PlusLevel' a) where
  type SubstArg (PlusLevel' a) = SubstArg a
  applySubst rho (Plus n l) = Plus n $ applySubst rho l

instance Subst Name where
  type SubstArg Name = Term
  applySubst rho = id

instance Subst ConPatternInfo where
  type SubstArg ConPatternInfo = Term
  applySubst rho i = i{ conPType = applySubst rho $ conPType i }

instance Subst Pattern where
  type SubstArg Pattern = Term
  applySubst rho = \case
    ConP c mt ps    -> ConP c (applySubst rho mt) $ applySubst rho ps
    DefP o q ps     -> DefP o q $ applySubst rho ps
    DotP o t        -> DotP o $ applySubst rho t
    p@(VarP _o _x)  -> p
    p@(LitP _o _l)  -> p
    p@(ProjP _o _x) -> p
    IApplyP o t u x -> IApplyP o (applySubst rho t) (applySubst rho u) x

instance Subst A.ProblemEq where
  type SubstArg A.ProblemEq = Term
  applySubst rho (A.ProblemEq p v a) =
    uncurry (A.ProblemEq p) $ applySubst rho (v,a)

instance DeBruijn BraveTerm where
  deBruijnVar = BraveTerm . deBruijnVar
  deBruijnView = deBruijnView . unBrave

instance DeBruijn NLPat where
  deBruijnVar i = PVar i []
  deBruijnView = \case
    PVar i []   -> Just i
    PVar{}      -> Nothing
    PDef{}      -> Nothing
    PLam{}      -> Nothing
    PPi{}       -> Nothing
    PSort{}     -> Nothing
    PBoundVar{} -> Nothing -- or... ?
    PTerm{}     -> Nothing -- or... ?

applyNLPatSubst :: TermSubst a => Substitution' NLPat -> a -> a
applyNLPatSubst = applySubst . fmap nlPatToTerm
  where
    nlPatToTerm :: NLPat -> Term
    nlPatToTerm = \case
      PVar i xs      -> Var i $ map (Apply . fmap var) xs
      PTerm u        -> u
      PDef f es      -> __IMPOSSIBLE__
      PLam i u       -> __IMPOSSIBLE__
      PPi a b        -> __IMPOSSIBLE__
      PSort s        -> __IMPOSSIBLE__
      PBoundVar i es -> __IMPOSSIBLE__

applyNLSubstToDom :: SubstWith NLPat a => Substitution' NLPat -> Dom a -> Dom a
applyNLSubstToDom rho dom = applySubst rho <$> dom{ domTactic = applyNLPatSubst rho $ domTactic dom }

instance Subst NLPat where
  type SubstArg NLPat = NLPat
  applySubst rho = \case
    PVar i bvs     -> lookupS rho i `applyBV` bvs
    PDef f es      -> PDef f $ applySubst rho es
    PLam i u       -> PLam i $ applySubst rho u
    PPi a b        -> PPi (applyNLSubstToDom rho a) (applySubst rho b)
    PSort s        -> PSort $ applySubst rho s
    PBoundVar i es -> PBoundVar i $ applySubst rho es
    PTerm u        -> PTerm $ applyNLPatSubst rho u

    where
      applyBV :: NLPat -> [Arg Int] -> NLPat
      applyBV p ys = case p of
        PVar i xs      -> PVar i (xs ++ ys)
        PTerm u        -> PTerm $ u `apply` map (fmap var) ys
        PDef f es      -> __IMPOSSIBLE__
        PLam i u       -> __IMPOSSIBLE__
        PPi a b        -> __IMPOSSIBLE__
        PSort s        -> __IMPOSSIBLE__
        PBoundVar i es -> __IMPOSSIBLE__

instance Subst NLPType where
  type SubstArg NLPType = NLPat
  applySubst rho (NLPType s a) = NLPType (applySubst rho s) (applySubst rho a)

instance Subst NLPSort where
  type SubstArg NLPSort = NLPat
  applySubst rho = \case
    PUniv u l -> PUniv u $ applySubst rho l
    PInf f n  -> PInf f n
    PSizeUniv -> PSizeUniv
    PLockUniv -> PLockUniv
    PLevelUniv -> PLevelUniv
    PIntervalUniv -> PIntervalUniv

instance Subst RewriteRule where
  type SubstArg RewriteRule = NLPat
  applySubst rho (RewriteRule q gamma f ps rhs t c) =
    RewriteRule q (applyNLPatSubst rho gamma)
                f (applySubst (liftS n rho) ps)
                  (applyNLPatSubst (liftS n rho) rhs)
                  (applyNLPatSubst (liftS n rho) t)
                  c
    where n = size gamma

instance Subst a => Subst (Blocked a) where
  type SubstArg (Blocked a) = SubstArg a
  applySubst rho b = fmap (applySubst rho) b

instance Subst DisplayForm where
  type SubstArg DisplayForm = Term
  applySubst rho (Display n ps v) =
    Display n (applySubst (liftS n rho) ps)
              (applySubst (liftS n rho) v)

instance Subst DisplayTerm where
  type SubstArg DisplayTerm = Term
  applySubst rho (DTerm' v es)      = DTerm' (applySubst rho v) $ applySubst rho es
  applySubst rho (DDot' v es)       = DDot'  (applySubst rho v) $ applySubst rho es
  applySubst rho (DCon c ci vs)     = DCon c ci $ applySubst rho vs
  applySubst rho (DDef c es)        = DDef c $ applySubst rho es
  applySubst rho (DWithApp v vs es) = uncurry3 DWithApp $ applySubst rho (v, vs, es)

instance Subst a => Subst (Tele a) where
  type SubstArg (Tele a) = SubstArg a
  applySubst rho  EmptyTel         = EmptyTel
  applySubst rho (ExtendTel t tel) = uncurry ExtendTel $ applySubst rho (t, tel)

instance Subst Constraint where
  type SubstArg Constraint = Term

  applySubst rho = \case
    ValueCmp cmp a u v       -> ValueCmp cmp (rf a) (rf u) (rf v)
    ValueCmpOnFace cmp p t u v -> ValueCmpOnFace cmp (rf p) (rf t) (rf u) (rf v)
    ElimCmp ps fs a v e1 e2  -> ElimCmp ps fs (rf a) (rf v) (rf e1) (rf e2)
    SortCmp cmp s1 s2        -> SortCmp cmp (rf s1) (rf s2)
    LevelCmp cmp l1 l2       -> LevelCmp cmp (rf l1) (rf l2)
    IsEmpty r a              -> IsEmpty r (rf a)
    CheckSizeLtSat t         -> CheckSizeLtSat (rf t)
    FindInstance m cands     -> FindInstance m (rf cands)
    ResolveInstanceHead q    -> ResolveInstanceHead (rf q)
    c@UnBlock{}              -> c
    c@CheckFunDef{}          -> c
    HasBiggerSort s          -> HasBiggerSort (rf s)
    HasPTSRule a s           -> HasPTSRule (rf a) (rf s)
    CheckLockedVars a b c d  -> CheckLockedVars (rf a) (rf b) (rf c) (rf d)
    UnquoteTactic t h g      -> UnquoteTactic (rf t) (rf h) (rf g)
    CheckDataSort q s        -> CheckDataSort q (rf s)
    CheckMetaInst m          -> CheckMetaInst m
    CheckType t              -> CheckType (rf t)
    UsableAtModality cc ms mod m -> UsableAtModality cc (rf ms) mod (rf m)
    where
      rf :: forall a. TermSubst a => a -> a
      rf x = applySubst rho x

instance Subst CompareAs where
  type SubstArg CompareAs = Term
  applySubst rho (AsTermsOf a) = AsTermsOf $ applySubst rho a
  applySubst rho AsSizes       = AsSizes
  applySubst rho AsTypes       = AsTypes

instance Subst a => Subst (Elim' a) where
  type SubstArg (Elim' a) = SubstArg a
  applySubst rho = \case
    Apply v      -> Apply $ applySubst rho v
    IApply x y r -> IApply (applySubst rho x) (applySubst rho y) (applySubst rho r)
    e@Proj{}     -> e

instance Subst a => Subst (Abs a) where
  type SubstArg (Abs a) = SubstArg a
  applySubst rho (Abs x a)   = Abs x $ applySubst (liftS 1 rho) a
  applySubst rho (NoAbs x a) = NoAbs x $ applySubst rho a

instance Subst a => Subst (Arg a) where
  type SubstArg (Arg a) = SubstArg a
  applySubst IdS arg = arg
  applySubst rho arg = setFreeVariables unknownFreeVariables $ fmap (applySubst rho) arg

instance Subst a => Subst (Named name a) where
  type SubstArg (Named name a) = SubstArg a
  applySubst rho = fmap (applySubst rho)

instance (Subst a, Subst b, SubstArg a ~ SubstArg b) => Subst (Dom' a b) where
  type SubstArg (Dom' a b) = SubstArg a

  applySubst IdS dom = dom
  applySubst rho dom = setFreeVariables unknownFreeVariables $
    fmap (applySubst rho) dom{ domTactic = applySubst rho (domTactic dom) }
  {-# INLINABLE applySubst #-}

instance Subst LetBinding where
  type SubstArg LetBinding = Term
  applySubst rho (LetBinding o v t) = LetBinding o (applySubst rho v) (applySubst rho t)

instance Subst a => Subst (Maybe a) where
  type SubstArg (Maybe a) = SubstArg a

instance Subst a => Subst [a] where
  type SubstArg [a] = SubstArg a

instance (Ord k, Subst a) => Subst (Map k a) where
  type SubstArg (Map k a) = SubstArg a

instance Subst a => Subst (WithHiding a) where
  type SubstArg (WithHiding a) = SubstArg a

instance Subst () where
  type SubstArg () = Term
  applySubst _ _ = ()

instance (Subst a, Subst b, SubstArg a ~ SubstArg b) => Subst (a, b) where
  type SubstArg (a, b) = SubstArg a
  applySubst rho (x,y) = (applySubst rho x, applySubst rho y)

instance (Subst a, Subst b, Subst c, SubstArg a ~ SubstArg b, SubstArg b ~ SubstArg c) => Subst (a, b, c) where
  type SubstArg (a, b, c) = SubstArg a
  applySubst rho (x,y,z) = (applySubst rho x, applySubst rho y, applySubst rho z)

instance
  ( Subst a, Subst b, Subst c, Subst d
  , SubstArg a ~ SubstArg b
  , SubstArg b ~ SubstArg c
  , SubstArg c ~ SubstArg d
  ) => Subst (a, b, c, d) where
  type SubstArg (a, b, c, d) = SubstArg a
  applySubst rho (x,y,z,u) = (applySubst rho x, applySubst rho y, applySubst rho z, applySubst rho u)

instance Subst Candidate where
  type SubstArg Candidate = Term
  applySubst rho (Candidate q u t ov) = Candidate q (applySubst rho u) (applySubst rho t) ov

instance Subst EqualityView where
  type SubstArg EqualityView = Term
  applySubst rho = \case
    OtherType t          -> OtherType $ applySubst rho t
    IdiomType t          -> IdiomType $ applySubst rho t
    EqualityViewType eqt -> EqualityViewType $ applySubst rho eqt

instance Subst EqualityTypeData where
  type SubstArg EqualityTypeData = Term
  applySubst rho (EqualityTypeData s eq l t a b) = EqualityTypeData
    (applySubst rho s)
    eq
    (map (applySubst rho) l)
    (applySubst rho t)
    (applySubst rho a)
    (applySubst rho b)

instance DeBruijn a => DeBruijn (Pattern' a) where
  debruijnNamedVar n i             = varP $ debruijnNamedVar n i
  -- deBruijnView returns Nothing, to prevent consS and the like
  -- from dropping the names and origins when building a substitution.
  deBruijnView _                   = Nothing

fromPatternSubstitution :: PatternSubstitution -> Substitution
fromPatternSubstitution = fmap patternToTerm

applyPatSubst :: TermSubst a => PatternSubstitution -> a -> a
applyPatSubst = applySubst . fromPatternSubstitution


usePatOrigin :: PatOrigin -> Pattern' a -> Pattern' a
usePatOrigin o p = case patternInfo p of
  Nothing -> p
  Just i  -> usePatternInfo (i { patOrigin = o }) p

usePatternInfo :: PatternInfo -> Pattern' a -> Pattern' a
usePatternInfo i p = case patternOrigin p of
  Nothing         -> p
  Just PatOSplit  -> p
  Just PatOAbsurd -> p
  Just _          -> case p of
    (VarP _ x) -> VarP i x
    (DotP _ u) -> DotP i u
    (ConP c (ConPatternInfo _ r ft b l) ps)
      -> ConP c (ConPatternInfo i r ft b l) ps
    DefP _ q ps -> DefP i q ps
    (LitP _ l) -> LitP i l
    ProjP{} -> __IMPOSSIBLE__
    (IApplyP _ t u x) -> IApplyP i t u x

instance Subst DeBruijnPattern where
  type SubstArg DeBruijnPattern = DeBruijnPattern
  applySubst IdS = id
  applySubst rho = \case
    VarP i x     ->
      usePatternInfo i $
      useName (dbPatVarName x) $
      lookupS rho $ dbPatVarIndex x
    DotP i u     -> DotP i $ applyPatSubst rho u
    ConP c ci ps -> ConP c ci {conPType = applyPatSubst rho (conPType ci)} $ applySubst rho ps
    DefP i q ps  -> DefP i q $ applySubst rho ps
    p@(LitP _ _) -> p
    p@ProjP{}    -> p
    IApplyP i t u x ->
      case useName (dbPatVarName x) $ lookupS rho $ dbPatVarIndex x of
        IApplyP _ _ _ y -> IApplyP i (applyPatSubst rho t) (applyPatSubst rho u) y
        VarP  _ y       -> IApplyP i (applyPatSubst rho t) (applyPatSubst rho u) y
        _ -> __IMPOSSIBLE__
    where
      useName :: PatVarName -> DeBruijnPattern -> DeBruijnPattern
      useName n (VarP o x)
        | isUnderscore (dbPatVarName x)
        = VarP o $ x { dbPatVarName = n }
      useName _ x = x

instance Subst Range where
  type SubstArg Range = Term
  applySubst _ = id

---------------------------------------------------------------------------
-- * Projections
---------------------------------------------------------------------------

-- | @projDropParsApply proj o args = 'projDropPars' proj o `'apply'` args@
--
--   This function is an optimization, saving us from construction lambdas we
--   immediately remove through application.
projDropParsApply :: Projection -> ProjOrigin -> Relevance -> Args -> Term
projDropParsApply (Projection prop d r _ lams) o rel args =
  case initLast $ getProjLams lams of
    -- If we have no more abstractions, we must be a record field
    -- (projection applied already to record value).
    Nothing -> if proper then Def d $ map Apply args else __IMPOSSIBLE__
    Just (pars, Arg i y) ->
      let irr = isIrrelevant rel
          core
            | proper && not irr = Lam i $ Abs y $ Var 0 [Proj o d]
            | otherwise         = Lam i $ Abs y $ Def d [Apply $ Var 0 [] <$ r]
            -- Issue2226: get ArgInfo for principal argument from projFromType
      -- Now drop pars many args
          (pars', args') = dropCommon pars args
      -- We only have to abstract over the parameters that exceed the arguments.
      -- We only have to apply to the arguments that exceed the parameters.
      in List.foldr (\ (Arg ai x) -> Lam ai . NoAbs x) (core `apply` args') pars'
  where proper = isJust prop

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

-- ** Telescope view of a type

type TelView = TelV Type
data TelV a  = TelV { theTel :: Tele (Dom a), theCore :: a }
  deriving (Show, Functor)

deriving instance (TermSubst a, Eq  a) => Eq  (TelV a)
deriving instance (TermSubst a, Ord a) => Ord (TelV a)

-- | Takes off all exposed function domains from the given type.
--   This means that it does not reduce to expose @Pi@-types.
telView' :: Type -> TelView
telView' = telView'UpTo (-1)

-- | @telView'UpTo n t@ takes off the first @n@ exposed function types of @t@.
-- Takes off all (exposed ones) if @n < 0@.
telView'UpTo :: Int -> Type -> TelView
telView'UpTo 0 t = TelV EmptyTel t
telView'UpTo n t = case unEl t of
  Pi a b  -> absV a (absName b) $ telView'UpTo (n - 1) (absBody b)
  _       -> TelV EmptyTel t

-- | Add given binding to the front of the telescope.
absV :: Dom a -> ArgName -> TelV a -> TelV a
absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t


-- ** Creating telescopes from lists of types

-- | Turn a typed binding @(x1 .. xn : A)@ into a telescope.
bindsToTel' :: (Name -> a) -> [Name] -> Dom Type -> ListTel' a
bindsToTel' f []     t = []
bindsToTel' f (x:xs) t = fmap (f x,) t : bindsToTel' f xs (raise 1 t)

bindsToTel :: [Name] -> Dom Type -> ListTel
bindsToTel = bindsToTel' nameToArgName

bindsToTel'1 :: (Name -> a) -> List1 Name -> Dom Type -> ListTel' a
bindsToTel'1 f = bindsToTel' f . List1.toList

bindsToTel1 :: List1 Name -> Dom Type -> ListTel
bindsToTel1 = bindsToTel . List1.toList

-- | Turn a typed binding @(x1 .. xn : A)@ into a telescope.
namedBindsToTel :: [NamedArg Name] -> Type -> Telescope
namedBindsToTel []       t = EmptyTel
namedBindsToTel (x : xs) t =
  ExtendTel (t <$ domFromNamedArgName x) $ Abs (nameToArgName $ namedArg x) $ namedBindsToTel xs (raise 1 t)

namedBindsToTel1 :: List1 (NamedArg Name) -> Type -> Telescope
namedBindsToTel1 = namedBindsToTel . List1.toList

domFromNamedArgName :: NamedArg Name -> Dom ()
domFromNamedArgName x = () <$ domFromNamedArg (fmap forceName x)
  where
    -- If no explicit name is given we use the bound name for the label.
    forceName (Named Nothing x) = Named (Just $ WithOrigin Inserted $ Ranged (getRange x) $ nameToArgName x) x
    forceName x = x

-- ** Abstracting in terms and types

mkPiSort :: Dom Type -> Abs Type -> Sort
mkPiSort a b = piSort (unEl <$> a) (getSort $ unDom a) (getSort <$> b)

-- | @mkPi dom t = telePi (telFromList [dom]) t@
mkPi :: Dom (ArgName, Type) -> Type -> Type
mkPi !dom b = el $ Pi a (mkAbs x b)
  where
    x = fst $ unDom dom
    a = snd <$> dom
    el = El $ mkPiSort a (Abs x b)

mkLam :: Arg ArgName -> Term -> Term
mkLam a v = Lam (argInfo a) (Abs (unArg a) v)

lamView :: Term -> ([Arg ArgName], Term)
lamView (Lam h (Abs   x b)) = first (Arg h x :) $ lamView b
lamView (Lam h (NoAbs x b)) = first (Arg h x :) $ lamView (raise 1 b)
lamView t                   = ([], t)

unlamView :: [Arg ArgName] -> Term -> Term
unlamView xs b = foldr mkLam b xs

telePi' :: (Abs Type -> Abs Type) -> Telescope -> Type -> Type
telePi' reAbs = telePi where
  telePi EmptyTel          t = t
  telePi (ExtendTel u tel) t = el $ Pi u $ reAbs b
    where
      b  = (`telePi` t) <$> tel
      el = El $ mkPiSort u b

-- | Uses free variable analysis to introduce 'NoAbs' bindings.
telePi :: Telescope -> Type -> Type
telePi = telePi' reAbs

-- | Everything will be an 'Abs'.
telePi_ :: Telescope -> Type -> Type
telePi_ = telePi' id

-- | Only abstract the visible components of the telescope,
--   and all that bind variables.  Everything will be an 'Abs'!
-- Caution: quadratic time!

telePiVisible :: Telescope -> Type -> Type
telePiVisible EmptyTel t = t
telePiVisible (ExtendTel u tel) t
    -- If u is not declared visible and b can be strengthened, skip quantification of u.
    | notVisible u, NoAbs x t' <- b' = t'
    -- Otherwise, include quantification over u.
    | otherwise = El (mkPiSort u b) $ Pi u b
  where
    b  = tel <&> (`telePiVisible` t)
    b' = reAbs b

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
  teleNoAbs tel t = foldr (\ Dom{domInfo = ai, unDom = (x, _)} -> Lam ai . NoAbs x) t tel

instance TeleNoAbs Telescope where
  teleNoAbs tel = teleNoAbs $ telToList tel


-- ** Telescope typing

-- | Given arguments @vs : tel@ (vector typing), extract their individual types.
--   Returns @Nothing@ is @tel@ is not long enough.

typeArgsWithTel :: Telescope -> [Term] -> Maybe [Dom Type]
typeArgsWithTel _ []                         = return []
typeArgsWithTel (ExtendTel dom tel) (v : vs) = (dom :) <$> typeArgsWithTel (absApp tel v) vs
typeArgsWithTel EmptyTel{} (_:_)             = Nothing

---------------------------------------------------------------------------
-- * Clauses
---------------------------------------------------------------------------

-- | In compiled clauses, the variables in the clause body are relative to the
--   pattern variables (including dot patterns) instead of the clause telescope.
compiledClauseBody :: Clause -> Maybe Term
compiledClauseBody cl = applySubst (renamingR perm) $ clauseBody cl
  where perm = fromMaybe __IMPOSSIBLE__ $ clausePerm cl

---------------------------------------------------------------------------
-- * Syntactic equality and order
--
-- Needs weakening.
---------------------------------------------------------------------------

deriving instance Eq Substitution
deriving instance Ord Substitution

deriving instance Eq Sort
deriving instance Ord Sort
deriving instance Eq Level
deriving instance Ord Level
deriving instance Eq PlusLevel
deriving instance Eq NotBlocked
deriving instance Eq t => Eq (Blocked t)
deriving instance Eq CandidateKind
deriving instance Eq Candidate

deriving instance (Subst a, Eq a)  => Eq  (Tele a)
deriving instance (Subst a, Ord a) => Ord (Tele a)

-- Andreas, 2019-11-16, issue #4201: to avoid potential unintended
-- performance loss, the Eq instance for Constraint is disabled:
--
-- -- deriving instance Eq Constraint
--
-- I am tempted to write
--
--   instance Eq Constraint where (==) = undefined
--
-- but this does not give a compilation error anymore when trying
-- to use equality on constraints.
-- Therefore, I hope this comment is sufficient to prevent a resurrection
-- of the Eq instance for Constraint.

deriving instance Eq Section

instance Ord PlusLevel where
  -- Compare on the atom first. Makes most sense for levelMax.
  compare (Plus n a) (Plus m b) = compare (a,n) (b,m)

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
  Dummy{}    == Dummy{}      = True
  _          == _            = False

instance Eq a => Eq (Pattern' a) where
  VarP _ x        == VarP _ y          = x == y
  DotP _ u        == DotP _ v          = u == v
  ConP c _ ps     == ConP c' _ qs      = c == c && ps == qs
  LitP _ l        == LitP _ l'         = l == l'
  ProjP _ f       == ProjP _ g         = f == g
  IApplyP _ u v x == IApplyP _ u' v' y = u == u' && v == v' && x == y
  DefP _ f ps     == DefP _ g qs       = f == g && ps == qs
  _               == _                 = False

instance Ord Term where
  Var a b    `compare` Var x y    = compare (x, b) (a, y)
                                    -- sort de Bruijn indices down (#2765)
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
  DontCare{} `compare` _          = LT
  _          `compare` DontCare{} = GT
  Dummy{}    `compare` Dummy{}    = EQ

-- Andreas, 2017-10-04, issue #2775, ignore irrelevant arguments during with-abstraction.
--
-- For reasons beyond my comprehension, the following Eq instances are not employed
-- by with-abstraction in TypeChecking.Abstract.isPrefixOf.
-- Instead, I modified the general Eq instance for Arg to ignore the argument
-- if irrelevant.

-- -- | Ignore irrelevant arguments in equality check.
-- --   Also ignore origin.
-- instance {-# OVERLAPPING #-} Eq (Arg Term) where
--   a@(Arg (ArgInfo h r _o) t) == a'@(Arg (ArgInfo h' r' _o') t') = trace ("Eq (Arg Term) on " ++ show a ++ " and " ++ show a') $
--     h == h' && ((r == Irrelevant) || (r' == Irrelevant) || (t == t'))
--     -- Andreas, 2017-10-04: According to Syntax.Common, equality on Arg ignores Relevance and Origin.

-- instance {-# OVERLAPPING #-} Eq Args where
--   us == vs = length us == length vs && and (zipWith (==) us vs)

-- instance {-# OVERLAPPING #-} Eq Elims where
--   us == vs = length us == length vs && and (zipWith (==) us vs)

-- | Equality of binders relies on weakening
--   which is a special case of renaming
--   which is a special case of substitution.
instance (Subst a, Eq a) => Eq (Abs a) where
  NoAbs _ a == NoAbs _ b = a == b  -- no need to raise if both are NoAbs
  a         == b         = absBody a == absBody b

instance (Subst a, Ord a) => Ord (Abs a) where
  NoAbs _ a `compare` NoAbs _ b = a `compare` b  -- no need to raise if both are NoAbs
  a         `compare` b         = absBody a `compare` absBody b

deriving instance Ord a => Ord (Dom a)

instance (Subst a, Eq a)  => Eq  (Elim' a) where
  Apply  a == Apply  b = a == b
  Proj _ x == Proj _ y = x == y
  IApply x y r == IApply x' y' r' = x == x' && y == y' && r == r'
  _ == _ = False

instance (Subst a, Ord a) => Ord (Elim' a) where
  Apply  a `compare` Apply  b = a `compare` b
  Proj _ x `compare` Proj _ y = x `compare` y
  IApply x y r `compare` IApply x' y' r' = compare x x' `mappend` compare y y' `mappend` compare r r'
  Apply{}  `compare` _        = LT
  _        `compare` Apply{}  = GT
  Proj{}   `compare` _        = LT
  _        `compare` Proj{}   = GT


---------------------------------------------------------------------------
-- * Sort stuff
---------------------------------------------------------------------------

-- | @univSort' univInf s@ gets the next higher sort of @s@, if it is
--   known (i.e. it is not just @UnivSort s@).
--
--   Precondition: @s@ is reduced
univSort' :: Sort -> Either Blocker Sort
univSort' (Univ u l)   = Right $ Univ (univUniv u) $ levelSuc l
univSort' (Inf u n)    = Right $ Inf (univUniv u) $ 1 + n
univSort' SizeUniv     = Right $ Inf UType 0
univSort' LockUniv     = Right $ Type $ ClosedLevel 1
univSort' LevelUniv    = Right $ Type $ ClosedLevel 1
univSort' IntervalUniv = Right $ SSet $ ClosedLevel 1
univSort' (MetaS m _)  = Left neverUnblock
univSort' FunSort{}    = Left neverUnblock
univSort' PiSort{}     = Left neverUnblock
univSort' UnivSort{}   = Left neverUnblock
univSort' DefS{}       = Left neverUnblock
univSort' DummyS{}     = Left neverUnblock

univSort :: Sort -> Sort
univSort s = fromRight (const $ UnivSort s) $ univSort' s

sort :: Sort -> Type
sort s = El (univSort s) $ Sort s

ssort :: Level -> Type
ssort l = sort (SSet l)

-- | A sort can either be small (Set l, Prop l, Size, ...)  or large
--   (Setω n).
data SizeOfSort = SizeOfSort
  { szSortUniv :: Univ
  , szSortSize :: Integer
  }

pattern SmallSort :: Univ -> SizeOfSort
pattern SmallSort u = SizeOfSort u (-1)

pattern LargeSort :: Univ -> Integer -> SizeOfSort
-- What I want to write here is:
-- @
--   pattern LargeSort u n = SizeOfSort u n | n >= 0
-- @
-- But I have to write:
pattern LargeSort u n <- ((\ x@(SizeOfSort u n) -> guard (n >= 0) $> x) -> Just (SizeOfSort u n))
-- DON'T WORK:
-- pattern LargeSort u n <- (n >= 0 -> True)
-- pattern LargeSort u n <- (n >= 0 -> SizeOfSort u n)
-- pattern LargeSort u n <- ((>= 0) . szSortSize -> SizeOfSort u n)
  where LargeSort u n = SizeOfSort u n

{-# COMPLETE SmallSort, LargeSort #-}

-- | Returns @Left blocker@ for unknown (blocked) sorts, and otherwise
--   returns @Right s@ where @s@ indicates the size and fibrancy.
sizeOfSort :: Sort -> Either Blocker SizeOfSort
sizeOfSort = \case
  Univ u _     -> Right $ SmallSort u
  SizeUniv     -> Right $ SmallSort UType
  LockUniv     -> Right $ SmallSort UType
  LevelUniv    -> Right $ SmallSort UType
  IntervalUniv -> Right $ SmallSort USSet
  Inf u n      -> Right $ LargeSort u n
  MetaS m _    -> Left $ unblockOnMeta m
  FunSort{}    -> Left neverUnblock
  PiSort{}     -> Left neverUnblock
  UnivSort{}   -> Left neverUnblock
  DefS{}       -> Left neverUnblock
  DummyS{}     -> Left neverUnblock

isSmallSort :: Sort -> Bool
isSmallSort s = case sizeOfSort s of
  Right SmallSort{} -> True
  _                 -> False

-- | Compute the sort of a function type from the sorts of its domain and codomain.
--
--   This function should only be called on reduced sorts,
--   since the @LevelUniv@ rules should only apply when the sort does not reduce to @Set@.
funSort' :: Sort -> Sort -> Either Blocker Sort
-- Andreas, 2023-05-12, AIM XXXVI, pri #6623:
-- On GHC 8.6 and 8.8 this pattern matching triggers warning
-- "Pattern match checker exceeded (2000000) iterations in a case alternative."
-- No clue how to turn off this warning, so we have to turn off -Werror for GHC < 8.10.
funSort' = curry \case
  (Univ u a      , Univ u' b    ) -> Right $ Univ (funUniv u u') $ levelLub a b
  (Inf ua m      , b            ) -> sizeOfSort b <&> \ (SizeOfSort ub n) -> Inf (funUniv ua ub) (max m n)
  (a             , Inf ub n     ) -> sizeOfSort a <&> \ (SizeOfSort ua m) -> Inf (funUniv ua ub) (max m n)
  (LockUniv      , LevelUniv    ) -> Left neverUnblock
  (LockUniv      , b            ) -> Right b
  -- No functions into lock types
  (a             , LockUniv     ) -> Left neverUnblock
  -- @IntervalUniv@ behaves like @SSet@, but functions into @Type@ land in @Type@
  (IntervalUniv  , IntervalUniv ) -> Right $ SSet $ ClosedLevel 0
  (IntervalUniv  , Univ u b     ) -> Right $ Univ u b
  (IntervalUniv  , _            ) -> Left neverUnblock
  (Univ u a      , IntervalUniv ) -> Right $ SSet $ a
  (_             , IntervalUniv ) -> Left neverUnblock
  (SizeUniv      , b            ) -> Right b
  (a             , SizeUniv     ) -> sizeOfSort a >>= \case
    SmallSort{} -> Right SizeUniv
    LargeSort{} -> Left neverUnblock
  -- No need to handle @LevelUniv@ in a special way here when --level-universe isn't on,
  -- since this function is currently always called after reduction.
  -- It would be safer to take it into account here, but would imply passing the option along as an argument.
  (LevelUniv     , LevelUniv    ) -> Right LevelUniv
  (_             , LevelUniv    ) -> Left neverUnblock
  (LevelUniv     , b            ) -> sizeOfSort b <&> \case
    SmallSort ub -> Inf ub 0
    LargeSort{}  -> b
  (MetaS m _     , _            ) -> Left $ unblockOnMeta m
  (_             , MetaS m _    ) -> Left $ unblockOnMeta m
  (FunSort{}     , _            ) -> Left neverUnblock
  (_             , FunSort{}    ) -> Left neverUnblock
  (PiSort{}      , _            ) -> Left neverUnblock
  (_             , PiSort{}     ) -> Left neverUnblock
  (UnivSort{}    , _            ) -> Left neverUnblock
  (_             , UnivSort{}   ) -> Left neverUnblock
  (DefS{}        , _            ) -> Left neverUnblock
  (_             , DefS{}       ) -> Left neverUnblock
  (DummyS{}      , _            ) -> Left neverUnblock
  (_             , DummyS{}     ) -> Left neverUnblock

funSort :: Sort -> Sort -> Sort
funSort a b = fromRight (const $ FunSort a b) $ funSort' a b

-- | Compute the sort of a pi type from the sorts of its domain
--   and codomain.
-- This function should only be called on reduced sorts, since the @LevelUniv@ rules should only apply when the sort doesn't reduce to @Set@
piSort' :: Dom Term -> Sort -> Abs Sort -> Either Blocker Sort
piSort' a s1       (NoAbs _ s2) = Right $ FunSort s1 s2
piSort' a s1 s2Abs@(Abs   _ s2) = case flexRigOccurrenceIn 0 s2 of
  Nothing -> Right $ FunSort s1 $ noabsApp __IMPOSSIBLE__ s2Abs
  Just o  -> case (sizeOfSort s1 , sizeOfSort s2) of
    (Right (SmallSort u1) , Right (SmallSort u2)) -> case o of
      StronglyRigid -> Right $ Inf (funUniv u1 u2) 0
      Unguarded     -> Right $ Inf (funUniv u1 u2) 0
      WeaklyRigid   -> Right $ Inf (funUniv u1 u2) 0
      Flexible ms   -> Left $ metaSetToBlocker ms
    (Right (LargeSort u1 n) , Right (SmallSort u2)) -> Right $ Inf (funUniv u1 u2) n
    (_                     , Right LargeSort{}    ) ->
       -- large sorts cannot depend on variables
       __IMPOSSIBLE__
       -- (`trace` __IMPOSSIBLE__) $ unlines
       --   [ "piSort': unexpected dependency in large codomain s2"
       --   , "- a  = " ++ prettyShow a
       --   , "- s1 = " ++ prettyShow s1
       --   , "- s2 = " ++ prettyShow s2
       --   , "- s2 (raw) = " ++ show s2
       --   ]
    (Left blocker          , Right _              ) -> Left blocker
    (Right _               , Left blocker         ) -> Left blocker
    (Left blocker1         , Left blocker2        ) -> Left $ unblockOnBoth blocker1 blocker2

-- Andreas, 2019-06-20
-- KEEP the following commented out code for the sake of the discussion on irrelevance.
-- piSort' a bAbs@(Abs   _ b) = case occurrence 0 b of
--     -- Andreas, Jesper, AIM XXIX, 2019-03-18, issue #3631
--     -- Remember the NoAbs here!
--     NoOccurrence  -> Just $ funSort a $ noabsApp __IMPOSSIBLE__ bAbs
--     -- Andreas, 2017-01-18, issue #2408:
--     -- The sort of @.(a : A) → Set (f a)@ in context @f : .A → Level@
--     -- is @dLub Set λ a → Set (lsuc (f a))@, but @DLub@s are not serialized.
--     -- Alternatives:
--     -- 1. -- Irrelevantly -> sLub s1 (absApp b $ DontCare $ Sort Prop)
--     --    We cheat here by simplifying the sort to @Set (lsuc (f *))@
--     --    where * is a dummy value.  The rationale is that @f * = f a@ (irrelevance!)
--     --    and that if we already have a neutral level @f a@
--     --    it should not hurt to have @f *@ even if type @A@ is empty.
--     --    However: sorts are printed in error messages when sorts do not match.
--     --    Also, sorts with a dummy like Prop would be ill-typed.
--     -- 2. We keep the DLub, and serialize it.
--     --    That's clean and principled, even though DLubs make level solving harder.
--     -- Jesper, 2018-04-20: another alternative:
--     -- 3. Return @Inf@ as in the relevant case. This is conservative and might result
--     --    in more occurrences of @Setω@ than desired, but at least it doesn't pollute
--     --    the sort system with new 'exotic' sorts.
--     Irrelevantly  -> Just Inf
--     StronglyRigid -> Just Inf
--     Unguarded     -> Just Inf
--     WeaklyRigid   -> Just Inf
--     Flexible _    -> Nothing

piSort :: Dom Term -> Sort -> Abs Sort -> Sort
piSort a s1 s2 = fromRight (const $ PiSort a s1 s2) $ piSort' a s1 s2

---------------------------------------------------------------------------
-- * Level stuff
---------------------------------------------------------------------------

-- ^ Computes @n0 ⊔ a₁ ⊔ a₂ ⊔ ... ⊔ aₙ@ and return its canonical form.
levelMax :: Integer -> [PlusLevel] -> Level
levelMax !n0 as0 = Max n as
  where
    -- step 1: flatten nested @Level@ expressions in @PlusLevel@s
    Max n1 as1 = expandLevel $ Max n0 as0
    -- step 2: remove subsumed @PlusLevel@s and sort what remains
    as        = removeSubsumed as1
    -- step 3: set constant to 0 if it is subsumed by one of the @PlusLevel@s
    greatestB = Prelude.maximum $ 0 : [ n | Plus n _ <- as ]
    n | n1 > greatestB = n1
      | otherwise      = 0

    lmax :: Integer -> [PlusLevel] -> [Level] -> Level
    lmax m as []              = Max m as
    lmax m as (Max n bs : ls) = lmax (max m n) (bs ++ as) ls

    expandLevel :: Level -> Level
    expandLevel (Max m as) = lmax m [] $ map expandPlus as

    expandPlus :: PlusLevel -> Level
    expandPlus (Plus m l) = levelPlus m (expandTm l)

    expandTm (Level l)       = expandLevel l
    expandTm l               = atomicLevel l

    removeSubsumed =
      map (\(a, n) -> Plus n a) .
      MapS.toAscList .
      MapS.fromListWith max .
      map (\(Plus n a) -> (a, n))

-- | Given two levels @a@ and @b@, compute @a ⊔ b@ and return its
--   canonical form.
levelLub :: Level -> Level -> Level
levelLub (Max m as) (Max n bs) = levelMax (max m n) $ as ++ bs

levelTm :: Level -> Term
levelTm l =
  case l of
    Max 0 [Plus 0 l] -> l
    _                -> Level l
