{-# LANGUAGE CPP, PatternGuards, TupleSections,
    TypeSynonymInstances, FlexibleInstances, OverlappingInstances,
    DeriveDataTypeable, DeriveFunctor, StandaloneDeriving #-}
module Agda.TypeChecking.Substitute where

import Control.Arrow ((***))

import Data.Typeable (Typeable)
import Data.List hiding (sort, drop)
import qualified Data.List as List
import Data.Function
import Data.Map (Map)

import Debug.Trace (trace)

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Base as Base
import Agda.TypeChecking.Free as Free
import Agda.TypeChecking.CompiledClause

import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../undefined.h"
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

instance Apply Term where
  applyE m [] = m
  applyE m es =
    case m of
      Var i es'   -> Var i (es' ++ es)
      Def f es'   -> defApp f es' es  -- remove projection redexes
      Con c args  -> conApp c args es
      Lam _ b     ->
        case es of
          Apply a : es0 -> absApp b (unArg a) `applyE` es0
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
    (Con (ConHead _ fs) vs) -> do
      i <- elemIndex f fs
      mhead (drop i vs)
    _ -> Nothing

-- | Eliminate a constructed term.
conApp :: ConHead -> Args -> Elims -> Term
conApp ch                args []             = Con ch args
conApp ch                args (Apply a : es) = conApp ch (args ++ [a]) es
conApp ch@(ConHead c fs) args (Proj f  : es) =
  let failure = flip trace __IMPOSSIBLE__ $
        "conApp: constructor " ++ show c ++
        " with fields " ++ show fs ++
        " projected by " ++ show f
      i = maybe failure id            $ elemIndex f fs
      v = maybe failure argToDontCare $ mhead $ drop i args
  in  applyE v es
{-
      i = maybe failure id    $ elemIndex f $ map unArg fs
      v = maybe failure unArg $ mhead $ drop i args
      -- Andreas, 2013-10-20 see Issue543a:
      -- protect result of irrelevant projection.
      r = maybe __IMPOSSIBLE__ getRelevance $ mhead $ drop i fs
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
argToDontCare :: Common.Arg c Term -> Term
argToDontCare (Common.Arg ai v)
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

instance Subst a => Apply (Tele a) where
  apply tel               []       = tel
  apply EmptyTel          _        = __IMPOSSIBLE__
  apply (ExtendTel _ tel) (t : ts) = absApp tel (unArg t) `apply` ts

instance Apply Definition where
  apply (Defn info x t pol occ df m c d) args = Defn info x (piApply t args) (apply pol args) (apply occ args) df m c (apply d args)

instance Apply [Base.Occurrence] where
  apply occ args = List.drop (length args) occ

instance Apply [Polarity] where
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
            , funProjection = Just p} ->
      case p `apply` args of
        p@Projection{ projIndex = n }
          | n < 0     -> __IMPOSSIBLE__
          -- case: applied only to parameters
          | n > 0     -> d { funProjection = Just p }
          -- case: applied also to record value
          | otherwise ->
              d { funClauses        = apply cs args'
                , funCompiled       = apply cc args'
                , funInv            = apply inv args'
                , funProjection     = Nothing -- WAS: Just $ p { projIndex = 0 }
                }
              where args' = [last args]  -- the record value
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
    apply (Clause r tel perm ps b t) args =
      Clause r
             (apply tel args)
             (apply perm args)
             (List.drop (size args) ps)
             (apply b args)
             (applySubst (parallelS (map unArg args)) t)

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
  apply (Branches cs ls m) args =
    Branches (apply cs args) (apply ls args) (apply m args)
  applyE (Branches cs ls m) es =
    Branches (applyE cs es) (applyE ls es) (applyE m es)

instance Apply FunctionInverse where
  apply NotInjective  args = NotInjective
  apply (Inverse inv) args = Inverse $ apply inv args

instance Apply ClauseBody where
  apply  b       []       = b
  apply (Bind b) (a:args) = absApp b (unArg a) `apply` args
  apply (Body v) args     = Body $ v `apply` args
  apply  NoBody   _       = NoBody
  applyE  b       []             = b

  applyE (Bind b) (Apply a : es) = absApp b (unArg a) `applyE` es
  applyE (Bind b) (Proj{}  : es) = __IMPOSSIBLE__
  applyE (Body v) es             = Body $ v `applyE` es
  applyE  NoBody   _             = NoBody

instance Apply DisplayTerm where
  apply (DTerm v)          args = DTerm $ apply v args
  apply (DDot v)           args = DDot  $ apply v args
  apply (DCon c vs)        args = DCon c $ vs ++ map (fmap DTerm) args
  apply (DDef c vs)        args = DDef c $ vs ++ map (fmap DTerm) args
  apply (DWithApp v args') args = DWithApp v $ args' ++ args

instance Apply t => Apply [t] where
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
piApply (El _ (Pi  _ b)) (a:args) = absApp b (unArg a) `piApply` args
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
  abstract  EmptyTel            tel = tel
  abstract (ExtendTel arg tel') tel = ExtendTel arg $ fmap (`abstract` tel) tel'

instance Abstract Definition where
  abstract tel (Defn info x t pol occ df m c d) =
    Defn info x (abstract tel t) (abstract tel pol) (abstract tel occ) df m c (abstract tel d)

instance Abstract [Base.Occurrence] where
  abstract tel []  = []
  abstract tel occ = replicate (size tel) Mixed ++ occ -- TODO: check occurrence

instance Abstract [Polarity] where
  abstract tel []  = []
  abstract tel pol = replicate (size tel) Invariant ++ pol -- TODO: check polarity

instance Abstract Projection where
  abstract tel p = p
    { projIndex    = size tel + projIndex p
    , projDropPars = abstract tel $ projDropPars p
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
    Function{ funProjection = Just p } ->
      d { funProjection = Just $ abstract tel p }
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
  abstract tel (Clause r tel' perm ps b t) =
    Clause r (abstract tel tel') (abstract tel perm)
           (namedTelVars tel ++ ps) (abstract tel b)
           t -- nothing to do for t, since it lives under the telescope

instance Abstract CompiledClauses where
  abstract tel Fail = Fail
  abstract tel (Done xs t) = Done (map (argFromDom . fmap fst) (telToList tel) ++ xs) t
  abstract tel (Case n bs) =
    Case (n + fromIntegral (size tel)) (abstract tel bs)

instance Abstract a => Abstract (WithArity a) where
  abstract tel (WithArity n a) = WithArity n $ abstract tel a

instance Abstract a => Abstract (Case a) where
  abstract tel (Branches cs ls m) =
    Branches (abstract tel cs) (abstract tel ls) (abstract tel m)

telVars :: Telescope -> [Arg Pattern]
telVars = map (fmap namedThing) . namedTelVars

namedTelVars :: Telescope -> [NamedArg Pattern]
namedTelVars EmptyTel                            = []
namedTelVars (ExtendTel (Common.Dom info a) tel) =
  Common.Arg info (Named (Just $ absName tel) $ VarP $ absName tel) :
  namedTelVars (unAbs tel)

instance Abstract FunctionInverse where
  abstract tel NotInjective  = NotInjective
  abstract tel (Inverse inv) = Inverse $ abstract tel inv

instance Abstract ClauseBody where
  abstract EmptyTel          b = b
  abstract (ExtendTel _ tel) b = Bind $ fmap (`abstract` b) tel

instance Abstract t => Abstract [t] where
  abstract tel = map (abstract tel)

instance Abstract t => Abstract (Maybe t) where
  abstract tel x = fmap (abstract tel) x

instance Abstract v => Abstract (Map k v) where
  abstract tel m = fmap (abstract tel) m

abstractArgs :: Abstract a => Args -> a -> a
abstractArgs args x = abstract tel x
    where
        tel   = foldr (\(Common.Arg info x) -> ExtendTel (Common.Dom info $ sort Prop) . Abs x)
                      EmptyTel
              $ zipWith (fmap . const) names args
        names = cycle $ map (:[]) ['a'..'z']

---------------------------------------------------------------------------
-- * Explicit substitutions
---------------------------------------------------------------------------

-- | Substitutions.

infixr 4 :#
data Substitution

  = IdS                     -- Γ ⊢ IdS : Γ

  | EmptyS                  -- Γ ⊢ EmptyS : ()

                            --      Γ ⊢ ρ : Δ
  | Wk !Int Substitution    -- -------------------
                            -- Γ, Ψ ⊢ Wk |Ψ| ρ : Δ

                            -- Γ ⊢ u : Aρ  Γ ⊢ ρ : Δ
  | Term :# Substitution    -- ---------------------
                            --   Γ ⊢ u :# ρ : Δ, A

                            --        Γ ⊢ ρ : Δ
  | Lift !Int Substitution  -- -------------------------
                            -- Γ, Ψρ ⊢ Lift |Ψ| ρ : Δ, Ψ
  deriving (Eq, Ord, Show)

idS :: Substitution
idS = IdS

wkS :: Int -> Substitution -> Substitution
wkS 0 rho        = rho
wkS n (Wk m rho) = Wk (n + m) rho
wkS n EmptyS     = EmptyS
wkS n rho        = Wk n rho

raiseS :: Int -> Substitution
raiseS n = wkS n idS

singletonS :: Term -> Substitution
singletonS u = u :# idS

liftS :: Int -> Substitution -> Substitution
liftS 0 rho          = rho
liftS k IdS          = IdS
liftS k (Lift n rho) = Lift (n + k) rho
liftS k rho          = Lift k rho

dropS :: Int -> Substitution -> Substitution
dropS 0 rho          = rho
dropS n IdS          = raiseS n
dropS n (Wk m rho)   = wkS m (dropS n rho)
dropS n (u :# rho)   = dropS (n - 1) rho
dropS n (Lift 0 rho) = __IMPOSSIBLE__
dropS n (Lift m rho) = wkS 1 $ dropS (n - 1) $ liftS (m - 1) rho
dropS n EmptyS       = __IMPOSSIBLE__

-- | @applySubst (ρ `composeS` σ) v == applySubst ρ (applySubst σ v)@
composeS :: Substitution -> Substitution -> Substitution
composeS rho IdS = rho
composeS IdS sgm = sgm
composeS rho EmptyS = EmptyS
composeS rho (Wk n sgm) = composeS (dropS n rho) sgm
composeS rho (u :# sgm) = applySubst rho u :# composeS rho sgm
composeS rho (Lift 0 sgm) = __IMPOSSIBLE__
composeS (u :# rho) (Lift n sgm) = u :# composeS rho (liftS (n - 1) sgm)
composeS rho (Lift n sgm) = lookupS rho 0 :# composeS rho (wkS 1 (liftS (n - 1) sgm))

-- If Γ ⊢ ρ : Δ, Θ then splitS |Θ| ρ = (σ, δ), with
--   Γ ⊢ σ : Δ
--   Γ ⊢ δ : Θσ
splitS :: Int -> Substitution -> (Substitution, Substitution)
splitS 0 rho          = (rho, EmptyS)
splitS n (u :# rho)   = id *** (u :#) $ splitS (n - 1) rho
splitS n (Lift 0 _)   = __IMPOSSIBLE__
splitS n (Wk m rho)   = wkS m *** wkS m $ splitS n rho
splitS n IdS          = (raiseS n, liftS n EmptyS)
splitS n (Lift m rho) = wkS 1 *** liftS 1 $ splitS (n - 1) (liftS (m - 1) rho)
splitS n EmptyS       = __IMPOSSIBLE__

infixr 4 ++#

(++#) :: [Term] -> Substitution -> Substitution
us ++# rho = foldr (:#) rho us

parallelS :: [Term] -> Substitution
parallelS us = us ++# idS

lookupS :: Substitution -> Nat -> Term
lookupS rho i = case rho of
  IdS                    -> var i
  Wk n IdS               -> let j = i + n in
                            if  j < 0 then __IMPOSSIBLE__ else var j
  Wk n rho               -> applySubst (raiseS n) (lookupS rho i)
  u :# rho   | i == 0    -> u
             | i < 0     -> __IMPOSSIBLE__
             | otherwise -> lookupS rho (i - 1)
  Lift n rho | i < n     -> var i
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

class Subst t where
  applySubst :: Substitution -> t -> t

raise :: Subst t => Nat -> t -> t
raise = raiseFrom 0

raiseFrom :: Subst t => Nat -> Nat -> t -> t
raiseFrom n k = applySubst (liftS n $ raiseS k)

subst :: Subst t => Term -> t -> t
subst u t = substUnder 0 u t

substUnder :: Subst t => Nat -> Term -> t -> t
substUnder n u = applySubst (liftS n (singletonS u))

instance Subst Substitution where
  applySubst rho sgm = composeS rho sgm

instance Subst Term where
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

instance Subst a => Subst (Ptr a) where
  applySubst rho = fmap (applySubst rho)

instance Subst Type where
  applySubst rho (El s t) = applySubst rho s `El` applySubst rho t

instance Subst Sort where
  applySubst rho s = case s of
    Type n     -> levelSort $ sub n
    Prop       -> Prop
    Inf        -> Inf
    DLub s1 s2 -> DLub (sub s1) (sub s2)
    where sub x = applySubst rho x

instance Subst Level where
  applySubst rho (Max as) = Max $ applySubst rho as

instance Subst PlusLevel where
  applySubst rho l@ClosedLevel{} = l
  applySubst rho (Plus n l) = Plus n $ applySubst rho l

instance Subst LevelAtom where
  applySubst rho (MetaLevel m vs)   = MetaLevel m    $ applySubst rho vs
  applySubst rho (BlockedLevel m v) = BlockedLevel m $ applySubst rho v
  applySubst rho (NeutralLevel v)   = UnreducedLevel $ applySubst rho v
  applySubst rho (UnreducedLevel v) = UnreducedLevel $ applySubst rho v

instance Subst Bool where
  applySubst rho = id

instance Subst Pattern where
  applySubst rho p = case p of
    ConP c mt ps -> ConP c (applySubst rho mt) $ applySubst rho ps
    DotP t       -> DotP $ applySubst rho t
    VarP s       -> p
    LitP l       -> p
    ProjP _      -> p

instance Subst t => Subst (Blocked t) where
  applySubst rho b = fmap (applySubst rho) b

instance Subst DisplayForm where
  applySubst rho (Display n ps v) =
    Display n (applySubst (liftS 1 rho) ps)
              (applySubst (liftS n rho) v)

instance Subst DisplayTerm where
  applySubst rho (DTerm v)        = DTerm $ applySubst rho v
  applySubst rho (DDot v)         = DDot  $ applySubst rho v
  applySubst rho (DCon c vs)      = DCon c $ applySubst rho vs
  applySubst rho (DDef c vs)      = DDef c $ applySubst rho vs
  applySubst rho (DWithApp vs ws) = uncurry DWithApp $ applySubst rho (vs, ws)

instance Subst a => Subst (Tele a) where
  applySubst rho  EmptyTel         = EmptyTel
  applySubst rho (ExtendTel t tel) = uncurry ExtendTel $ applySubst rho (t, tel)

instance Subst Constraint where
  applySubst rho c = case c of
    ValueCmp cmp a u v       -> ValueCmp cmp (rf a) (rf u) (rf v)
    ElimCmp ps a v e1 e2     -> ElimCmp ps (rf a) (rf v) (rf e1) (rf e2)
    TypeCmp cmp a b          -> TypeCmp cmp (rf a) (rf b)
    TelCmp a b cmp tel1 tel2 -> TelCmp (rf a) (rf b) cmp (rf tel1) (rf tel2)
    SortCmp cmp s1 s2        -> SortCmp cmp (rf s1) (rf s2)
    LevelCmp cmp l1 l2       -> LevelCmp cmp (rf l1) (rf l2)
    Guarded c cs             -> Guarded (rf c) cs
    IsEmpty r a              -> IsEmpty r (rf a)
    FindInScope m cands      -> FindInScope m (rf cands)
    UnBlock{}                -> c
    where
      rf x = applySubst rho x

instance Subst Elim where
  applySubst rho e = case e of
    Apply v -> Apply (applySubst rho v)
    Proj{}  -> e

instance Subst a => Subst (Abs a) where
  applySubst rho (Abs x a)   = Abs x $ applySubst (liftS 1 rho) a
  applySubst rho (NoAbs x a) = NoAbs x $ applySubst rho a

instance Subst a => Subst (Arg a) where
  applySubst rho = fmap (applySubst rho)

instance Subst a => Subst (Named name a) where
  applySubst rho = fmap (applySubst rho)

instance Subst a => Subst (Dom a) where
  applySubst rho = fmap (applySubst rho)

instance Subst a => Subst (Maybe a) where
  applySubst rho = fmap (applySubst rho)

instance Subst a => Subst [a] where
  applySubst rho = map (applySubst rho)

instance Subst () where
  applySubst _ _ = ()

instance (Subst a, Subst b) => Subst (a,b) where
  applySubst rho (x,y) = (applySubst rho x, applySubst rho y)

instance Subst ClauseBody where
  applySubst rho (Body t) = Body $ applySubst rho t
  applySubst rho (Bind b) = Bind $ applySubst rho b
  applySubst _   NoBody   = NoBody

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

data TelV a = TelV { theTel :: Tele (Dom a), theCore :: a }
  deriving (Typeable, Show, Eq, Ord, Functor)

type TelView = TelV Type
type ListTel = [Dom (String, Type)]

telFromList :: ListTel -> Telescope
telFromList = foldr (\(Common.Dom info (x, a)) -> ExtendTel (Common.Dom info a) . Abs x)
                    EmptyTel

telToList :: Telescope -> ListTel
telToList EmptyTel = []
telToList (ExtendTel arg tel) = fmap (absName tel,) arg : telToList (absBody tel)

-- | Turn a typed binding @(x1 .. xn : A)@ into a telescope.
bindsToTel :: [Name] -> Dom Type -> ListTel
bindsToTel []     t = []
bindsToTel (x:xs) t = ((show $ nameConcrete x,) <$> t) : bindsToTel xs (raise 1 t)

telView' :: Type -> TelView
telView' t = case ignoreSharing $ unEl t of
  Pi a b  -> absV a (absName b) $ telView' (absBody b)
  _       -> TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

-- | @mkPi dom t = telePi (telFromList [dom]) t@
mkPi :: Dom (String, Type) -> Type -> Type
mkPi (Common.Dom info (x, a)) b = el $ Pi (Common.Dom info a) (mkAbs x b)
  where
    el = El $ dLub (getSort a) (Abs x (getSort b)) -- dLub checks x freeIn

telePi' :: (Abs Type -> Abs Type) -> Telescope -> Type -> Type
telePi' reAbs = telePi where
  telePi EmptyTel          t = t
  telePi (ExtendTel u tel) t = el $ Pi u $ reAbs b
    where
      b  = (`telePi` t) <$> tel
      s1 = getSort $ unDom u
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
teleLam  EmptyTel	  t = t
teleLam (ExtendTel u tel) t = Lam (domInfo u) $ flip teleLam t <$> tel

-- | Performs void ('noAbs') abstraction over telescope.
class TeleNoAbs a where
  teleNoAbs :: a -> Term -> Term

instance TeleNoAbs ListTel where
  teleNoAbs tel t = foldr (\ (Common.Dom ai (x, _)) -> Lam ai . NoAbs x) t tel

instance TeleNoAbs Telescope where
  teleNoAbs tel = teleNoAbs $ telToList tel

-- | Dependent least upper bound, to assign a level to expressions
--   like @forall i -> Set i@.
--
--   @dLub s1 \i.s2 = \omega@ if @i@ appears in the rigid variables of @s2@.
dLub :: Sort -> Abs Sort -> Sort
dLub s1 (NoAbs _ s2) = sLub s1 s2
dLub s1 b@(Abs _ s2) = case occurrence 0 $ freeVars s2 of
  Flexible      -> DLub s1 b
  Irrelevantly  -> DLub s1 b
  NoOccurrence  -> sLub s1 (absApp b __IMPOSSIBLE__)
--  Free.Unused   -> sLub s1 (absApp b __IMPOSSIBLE__) -- triggers Issue784
  Free.Unused   -> DLub s1 b
  StronglyRigid -> Inf
  WeaklyRigid   -> Inf

---------------------------------------------------------------------------
-- * Functions on abstractions
--   and things we couldn't do before we could define 'absBody'
---------------------------------------------------------------------------

-- | Instantiate an abstraction
absApp :: Subst t => Abs t -> Term -> t
absApp (Abs   _ v) u = subst u v
absApp (NoAbs _ v) _ = v

absBody :: Subst t => Abs t -> t
absBody (Abs   _ v) = v
absBody (NoAbs _ v) = raise 1 v

mkAbs :: (Subst a, Free a) => String -> a -> Abs a
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
underAbs cont a b = case b of
  Abs   x t -> Abs   x $ cont (raise 1 a) t
  NoAbs x t -> NoAbs x $ cont a t

-- | @underLambdas n k a b@ drops @n@ initial 'Lam's from @b@,
--   performs operation @k@ on @a@ and the body of @b@,
--   and puts the 'Lam's back.  @a@ is raised correctly
--   according to the number of abstractions.
underLambdas :: Subst a => Int -> (a -> Term -> Term) -> a -> Term -> Term
underLambdas n cont a v = loop n a v where
  loop 0 a v = cont a v
  loop n a v = case ignoreSharing v of
    Lam h b -> Lam h $ underAbs (loop $ n-1) a b
    _       -> __IMPOSSIBLE__

-- | @getBody@ returns the properly raised clause 'Body',
--   and 'Nothing' if 'NoBody'.
--
--   @getBodyUnraised@ just grabs the body, without raising the de Bruijn indices.
--   This is useful if you want to consider the body in context 'clauseTel'.
class GetBody a where
  getBody         :: a -> Maybe Term
  getBodyUnraised :: a -> Maybe Term

instance GetBody ClauseBody where
  getBody = body 0
    where
      -- collect all shiftings and do them in the end in one go
      body :: Int -> ClauseBody -> Maybe Term
      body _ NoBody             = Nothing
      body n (Body v)           = Just $ raise n v
      body n (Bind (NoAbs _ v)) = body n v
      body n (Bind (Abs   _ v)) = body (n + 1) v

  getBodyUnraised NoBody   = Nothing
  getBodyUnraised (Body v) = Just v
  getBodyUnraised (Bind b) = getBodyUnraised $ unAbs b  -- Does not raise!

instance GetBody Clause where
  getBody         = getBody         . clauseBody
  getBodyUnraised = getBodyUnraised . clauseBody

---------------------------------------------------------------------------
-- * Syntactic equality and order
---------------------------------------------------------------------------

deriving instance (Subst a, Eq a) => Eq (Tele a)
deriving instance (Subst a, Ord a) => Ord (Tele a)

deriving instance Eq Sort
deriving instance Ord Sort
deriving instance Eq Type
deriving instance Ord Type
deriving instance Eq Level
deriving instance Ord Level
deriving instance Eq PlusLevel
deriving instance Ord LevelAtom
deriving instance Eq Elim
deriving instance Ord Elim

deriving instance Eq Constraint

instance Ord PlusLevel where
  compare ClosedLevel{} Plus{}            = LT
  compare Plus{} ClosedLevel{}            = GT
  compare (ClosedLevel n) (ClosedLevel m) = compare n m
  -- Compare on the atom first. Makes most sense for levelMax.
  compare (Plus n a) (Plus m b)           = compare (a,n) (b,m)

instance Eq LevelAtom where
  (==) = (==) `on` unLevelAtom

-- | Syntactic equality, ignores stuff below @DontCare@.
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

instance (Subst a, Eq a) => Eq (Abs a) where
  NoAbs _ a == NoAbs _ b = a == b
  Abs   _ a == Abs   _ b = a == b
  a         == b         = absBody a == absBody b

instance (Subst a, Ord a) => Ord (Abs a) where
  NoAbs _ a `compare` NoAbs _ b = a `compare` b
  Abs   _ a `compare` Abs   _ b = a `compare` b
  a         `compare` b         = absBody a `compare` absBody b

---------------------------------------------------------------------------
-- * Level stuff
---------------------------------------------------------------------------

sLub :: Sort -> Sort -> Sort
sLub s Prop = s
sLub Prop s = s
sLub Inf _ = Inf
sLub _ Inf = Inf
sLub (Type (Max as)) (Type (Max bs)) = Type $ levelMax (as ++ bs)
sLub (DLub a b) c = DLub (sLub a c) b
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
    ns = case [ n | ClosedLevel n <- as, n > 0 ] of
      []  -> []
      ns  -> [ ClosedLevel n | n <- [Prelude.maximum ns], n > greatestB ]
    bs = subsume [ b | b@Plus{} <- as ]
    greatestB | null bs   = 0
              | otherwise = Prelude.maximum [ n | Plus n _ <- bs ]

    expand l@ClosedLevel{} = [l]
    expand (Plus n l) = map (plus n) $ expand0 $ expandAtom l

    expand0 [] = [ClosedLevel 0]
    expand0 as = as

    expandAtom l = case l of
      BlockedLevel _ v -> expandTm v
      NeutralLevel v   -> expandTm v
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
  | List.any isInf as = Inf
  where
    isInf ClosedLevel{}        = False
    isInf (Plus _ l)           = infAtom l
    infAtom (NeutralLevel a)   = infTm a
    infAtom (UnreducedLevel a) = infTm a
    infAtom MetaLevel{}        = False
    infAtom BlockedLevel{}     = False
    infTm (Sort Inf)           = True
    infTm (Shared p)           = infTm $ derefPtr p
    infTm _                    = False
levelSort l =
  case ignoreSharing $ levelTm l of
    Sort s -> s
    _      -> Type l

levelTm :: Level -> Term
levelTm l =
  case l of
    Max [Plus 0 l] -> unLevelAtom l
    _              -> Level l

unLevelAtom (MetaLevel x es)   = MetaV x es
unLevelAtom (NeutralLevel v)   = v
unLevelAtom (UnreducedLevel v) = v
unLevelAtom (BlockedLevel _ v) = v

---------------------------------------------------------------------------
-- * Boring instances
---------------------------------------------------------------------------

instance Sized Substitution where
  size IdS          = 1
  size EmptyS       = 1
  size (Wk _ rho)   = 1 + size rho
  size (t :# rho)   = 1 + size t + size rho
  size (Lift _ rho) = 1 + size rho

instance KillRange Substitution where
  killRange IdS          = IdS
  killRange EmptyS       = EmptyS
  killRange (Wk n rho)   = killRange1 (Wk n) rho
  killRange (t :# rho)   = killRange2 (:#) t rho
  killRange (Lift n rho) = killRange1 (Lift n) rho
