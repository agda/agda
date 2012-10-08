{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances, OverlappingInstances,
    DeriveDataTypeable, DeriveFunctor, StandaloneDeriving #-}
module Agda.TypeChecking.Substitute where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Arrow ((***))

import Data.Typeable (Typeable)
import Data.List hiding (sort)
import qualified Data.List as List
import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base as Base
import Agda.TypeChecking.Free as Free
import Agda.TypeChecking.CompiledClause

import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Apply something to a bunch of arguments.
--   Preserves blocking tags (application can never resolve blocking).
class Apply t where
    apply :: t -> Args -> t

instance Apply Term where
    apply m [] = m
    apply m args@(a:args0) =
        case m of
            Var i args'   -> Var i (args' ++ args)
            Def c args'   -> Def c (args' ++ args)
            Con c args'   -> Con c (args' ++ args)
            Lam _ u       -> absApp u (unArg a) `apply` args0
            MetaV x args' -> MetaV x (args' ++ args)
            Shared p      -> Shared $ apply p args
            Lit{}         -> __IMPOSSIBLE__
            Level{}       -> __IMPOSSIBLE__
            Pi _ _        -> __IMPOSSIBLE__
            Sort _        -> __IMPOSSIBLE__
            DontCare mv   -> DontCare $ mv `apply` args  -- Andreas, 2011-10-02
              -- need to go under DontCare, since "with" might resurrect irrelevant term

instance Apply Type where
  apply = piApply

instance Apply Sort where
  apply s [] = s
  apply s _  = __IMPOSSIBLE__

instance Apply a => Apply (Ptr a) where
  apply p xs = fmap (`apply` xs) p

instance Subst a => Apply (Tele a) where
  apply tel               []       = tel
  apply EmptyTel          _        = __IMPOSSIBLE__
  apply (ExtendTel _ tel) (t : ts) = absApp tel (unArg t) `apply` ts

instance Apply Definition where
  apply (Defn rel x t pol occ df m c d) args = Defn rel x (piApply t args) (apply pol args) (apply occ args) df m c (apply d args)

instance Apply [Base.Occurrence] where
  apply occ args = drop (length args) occ

instance Apply [Polarity] where
  apply pol args = drop (length args) pol

instance Apply Defn where
  apply d [] = d
  apply d args = case d of
    Axiom{} -> d
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Nothing {-, funArgOccurrences = occ -} } ->
      d { funClauses    = apply cs args
        , funCompiled   = apply cc args
        , funInv        = apply inv args
--        , funArgOccurrences = drop (length args) occ
        }
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Just (r, n) {-, funArgOccurrences = occ -} }
      | m < n  -> d { funProjection = Just (r, n - m) }
      | otherwise ->
        d { funClauses        = apply cs args'
          , funCompiled       = apply cc args'
          , funInv            = apply inv args'
          , funProjection     = Just (r, 0)
--          , funArgOccurrences = drop 1 occ
          }
      where args' = [last args]
            m = size args
    Datatype{ dataPars = np, dataClause = cl
            {-, dataArgOccurrences = occ-} } ->
      d { dataPars = np - size args, dataClause = apply cl args
--        , dataArgOccurrences = drop (length args) occ
        }
    Record{ recPars = np, recConType = t, recClause = cl, recTel = tel
          {-, recArgOccurrences = occ-} } ->
      d { recPars = np - size args, recConType = apply t args
        , recClause = apply cl args, recTel = apply tel args
--        , recArgOccurrences = drop (length args) occ
        }
    Constructor{ conPars = np } ->
      d { conPars = np - size args }
    Primitive{ primClauses = cs } ->
      d { primClauses = apply cs args }

instance Apply PrimFun where
    apply (PrimFun x ar def) args   = PrimFun x (ar - size args) $ \vs -> def (args ++ vs)

instance Apply Clause where
    apply (Clause r tel perm ps b) args =
      Clause r (apply tel args) (apply perm args)
             (drop (size args) ps) (apply b args)

instance Apply CompiledClauses where
  apply cc args = case cc of
    Fail     -> Fail
    Done hs t
      | length hs >= len -> Done (drop len hs)
                                 (substs ([ Var i []
                                          | i <- [0..length hs - len - 1]] ++
                                          map unArg args) t)
      | otherwise -> __IMPOSSIBLE__
    Case n bs
      | n >= len  -> Case (n - len) (apply bs args)
      | otherwise -> __IMPOSSIBLE__
    where
      len = length args

instance Apply a => Apply (Case a) where
  apply (Branches cs ls m) args =
    Branches (apply cs args) (apply ls args) (apply m args)

instance Apply FunctionInverse where
  apply NotInjective  args = NotInjective
  apply (Inverse inv) args = Inverse $ apply inv args

instance Apply ClauseBody where
    apply  b                 []       = b
    apply (Bind (Abs   _ b)) (a:args) = subst (unArg a) b `apply` args
    apply (Bind (NoAbs _ b)) (_:args) = b `apply` args
    apply (Body v)           args     = Body $ v `apply` args
    apply  NoBody             _       = NoBody

instance Apply DisplayTerm where
  apply (DTerm v)          args = DTerm $ apply v args
  apply (DDot v)           args = DDot  $ apply v args
  apply (DCon c vs)        args = DCon c $ vs ++ map (fmap DTerm) args
  apply (DDef c vs)        args = DDef c $ vs ++ map (fmap DTerm) args
  apply (DWithApp v args') args = DWithApp v $ args' ++ args

instance Apply t => Apply [t] where
    apply ts args = map (`apply` args) ts

instance Apply t => Apply (Blocked t) where
    apply b args = fmap (`apply` args) b

instance Apply t => Apply (Maybe t) where
  apply x args = fmap (`apply` args) x

instance Apply v => Apply (Map k v) where
  apply x args = fmap (`apply` args) x

instance (Apply a, Apply b) => Apply (a,b) where
    apply (x,y) args = (apply x args, apply y args)

instance (Apply a, Apply b, Apply c) => Apply (a,b,c) where
    apply (x,y,z) args = (apply x args, apply y args, apply z args)

instance Apply Permutation where
  -- The permutation must start with [0..m - 1]
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
piApply _ _                       = __IMPOSSIBLE__

-- | @(abstract args v) args --> v[args]@.
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
  abstract tel (Defn rel x t pol occ df m c d) =
    Defn rel x (abstract tel t) (abstract tel pol) (abstract tel occ) df m c (abstract tel d)

instance Abstract [Base.Occurrence] where
  abstract tel []  = []
  abstract tel occ = replicate (size tel) Mixed ++ occ -- TODO: check occurrence

instance Abstract [Polarity] where
  abstract tel []  = []
  abstract tel pol = replicate (size tel) Invariant ++ pol -- TODO: check polarity

instance Abstract Defn where
  abstract tel d = case d of
    Axiom{} -> d
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Nothing {-, funArgOccurrences = occ-} } ->
      d { funClauses = abstract tel cs, funCompiled = abstract tel cc
        , funInv = abstract tel inv
--        , funArgOccurrences = replicate (size tel) Mixed ++ occ -- TODO: check occurrence
        }
    Function{ funClauses = cs, funCompiled = cc, funInv = inv
            , funProjection = Just (r, n) {-, funArgOccurrences = occ-} } ->
      d { funProjection = Just (r, n + size tel) }
    Datatype{ dataPars = np, dataClause = cl {-, dataArgOccurrences = occ-} } ->
      d { dataPars = np + size tel, dataClause = abstract tel cl
--        , dataArgOccurrences = replicate (size tel) Mixed ++ occ -- TODO: check occurrence
        }
    Record{ recPars = np, recConType = t, recClause = cl, recTel = tel'
          {-, recArgOccurrences = occ-} } ->
      d { recPars = np + size tel, recConType = abstract tel t
        , recClause = abstract tel cl, recTel = abstract tel tel'
--        , recArgOccurrences = replicate (size tel) Mixed ++ occ -- TODO: check occurrence
        }
    Constructor{ conPars = np } ->
      d { conPars = np + size tel }
    Primitive{ primClauses = cs } ->
      d { primClauses = abstract tel cs }

instance Abstract PrimFun where
    abstract tel (PrimFun x ar def) = PrimFun x (ar + n) $ \ts -> def $ genericDrop n ts
        where n = size tel

instance Abstract Clause where
  abstract tel (Clause r tel' perm ps b) =
    Clause r (abstract tel tel') (abstract tel perm)
           (telVars tel ++ ps) (abstract tel b)

instance Abstract CompiledClauses where
  abstract tel Fail = Fail
  abstract tel (Done xs t) = Done (map (argFromDom . fmap fst) (telToList tel) ++ xs) t
  abstract tel (Case n bs) =
    Case (n + fromIntegral (size tel)) (abstract tel bs)

instance Abstract a => Abstract (Case a) where
  abstract tel (Branches cs ls m) =
    Branches (abstract tel cs) (abstract tel ls) (abstract tel m)

telVars :: Telescope -> [Arg Pattern]
telVars EmptyTel                    = []
telVars (ExtendTel (Dom h r a) tel) = Arg h r (VarP $ absName tel) : telVars (unAbs tel)

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
        tel   = foldr (\(Arg h r x) -> ExtendTel (Dom h r $ sort Prop) . Abs x) EmptyTel
              $ zipWith (fmap . const) names args
        names = cycle $ map (:[]) ['a'..'z']

-- | Substitutions.

type Substitution = [Term]

-- | Substitute a term for the nth free variable.
--
class Subst t where
    substs     :: Substitution -> t -> t
    substUnder :: Nat -> Term -> t -> t

idSub :: Telescope -> Substitution
idSub tel = map var [0 .. size tel - 1]

subst :: Subst t => Term -> t -> t
subst u t = substUnder 0 (shared u) t

instance Subst Term where
    substs [] t = t
    substs us t =
        case t of
            Var i vs    -> (us !!! i) `apply` substs us vs
            Lam h m     -> Lam h $ substs us m
            Def c vs    -> Def c $ substs us vs
            Con c vs    -> Con c $ substs us vs
            MetaV x vs  -> MetaV x $ substs us vs
            Lit l       -> Lit l
            Level l     -> levelTm $ substs us l
            Pi a b      -> uncurry Pi $ substs us (a,b)
            Sort s      -> sortTm $ substs us s
            Shared p    -> Shared $ substs us p
            DontCare mv -> DontCare $ substs us mv
        where
            []     !!! n = __IMPOSSIBLE__
            (x:xs) !!! 0 = x
            (_:xs) !!! n = xs !!! (n - 1)
    substUnder n u t =
        case t of
            Var i vs
              | i == n    -> raise n u `apply` substUnder n u vs
              | i < n     -> Var i $ substUnder n u vs
              | otherwise -> Var (i - 1) $ substUnder n u vs
            Lam h m    -> Lam h $ substUnder n u m
            Def c vs   -> Def c $ substUnder n u vs
            Con c vs   -> Con c $ substUnder n u vs
            MetaV x vs -> MetaV x $ substUnder n u vs
            Level l    -> levelTm $ substUnder n u l
            Lit l      -> Lit l
            Pi a b     -> uncurry Pi $ substUnder n u (a,b)
            Sort s     -> sortTm $ substUnder n u s
            Shared p    -> Shared $ substUnder n u p
            DontCare mv -> DontCare $ substUnder n u mv

instance Subst a => Subst (Ptr a) where
  substs us      = fmap (substs us)
  substUnder n u = fmap (substUnder n u)

instance Subst Type where
    substs us (El s t) = substs us s `El` substs us t
    substUnder n u (El s t) = substUnder n u s `El` substUnder n u t

instance Subst Sort where
    substs us s = case s of
      Type n     -> levelSort $ sub n
      Prop       -> Prop
      Inf        -> Inf
      DLub s1 s2 -> DLub (sub s1) (sub s2)
      where sub x = substs us x

    substUnder n u s = case s of
      Type n     -> levelSort $ sub n
      Prop       -> Prop
      Inf        -> Inf
      DLub s1 s2 -> DLub (sub s1) (sub s2)
      where sub x = substUnder n u x

instance Subst Level where
  substs us (Max as) = Max $ substs us as
  substUnder n u (Max as) = Max $ substUnder n u as

instance Subst PlusLevel where
  substs us l@ClosedLevel{} = l
  substs us (Plus n l) = Plus n $ substs us l
  substUnder n u l@ClosedLevel{} = l
  substUnder n u (Plus m l) = Plus m $ substUnder n u l

instance Subst LevelAtom where
  substs us      (MetaLevel m vs)   = MetaLevel m    $ substs us vs
  substs us      (BlockedLevel m v) = BlockedLevel m $ substs us v
  substs us      (NeutralLevel v)   = UnreducedLevel $ substs us v
  substs us      (UnreducedLevel v) = UnreducedLevel $ substs us v
  substUnder n u (MetaLevel m vs)   = MetaLevel m    $ substUnder n u vs
  substUnder n u (BlockedLevel m v) = BlockedLevel m $ substUnder n u v
  substUnder n u (NeutralLevel v)   = UnreducedLevel $ substUnder n u v
  substUnder n u (UnreducedLevel v) = UnreducedLevel $ substUnder n u v

instance Subst Pattern where
  substs us p = case p of
    VarP s       -> VarP s
    LitP l       -> LitP l
    ConP c mt ps -> ConP c (substs us mt) $ substs us ps
    DotP t       -> DotP $ substs us t
  substUnder n u p = case p of
    VarP s       -> VarP s
    LitP l       -> LitP l
    ConP c mt ps -> ConP c (substUnder n u mt) $ substUnder n u ps
    DotP t       -> DotP $ substUnder n u t

instance Subst t => Subst (Blocked t) where
    substs us b      = fmap (substs us) b
    substUnder n u b = fmap (substUnder n u) b

instance Subst DisplayTerm where
  substs us      (DTerm v)        = DTerm $ substs us v
  substs us      (DDot v)         = DDot  $ substs us v
  substs us      (DCon c vs)      = DCon c $ substs us vs
  substs us      (DDef c vs)      = DDef c $ substs us vs
  substs us      (DWithApp vs ws) = uncurry DWithApp $ substs us (vs, ws)
  substUnder n u (DTerm v)        = DTerm $ substUnder n u v
  substUnder n u (DDot  v)        = DDot  $ substUnder n u v
  substUnder n u (DCon c vs)      = DCon c $ substUnder n u vs
  substUnder n u (DDef c vs)      = DDef c $ substUnder n u vs
  substUnder n u (DWithApp vs ws) = uncurry DWithApp $ substUnder n u (vs, ws)

instance Subst a => Subst (Tele a) where
  substs us  EmptyTel              = EmptyTel
  substs us (ExtendTel t tel)      = uncurry ExtendTel $ substs us (t, tel)
  substUnder n u  EmptyTel         = EmptyTel
  substUnder n u (ExtendTel t tel) = uncurry ExtendTel $ substUnder n u (t, tel)

instance Subst a => Subst (Abs a) where
    substs us      (Abs   x t) = Abs   x $ substs (var 0 : raise 1 us) t
    substs us      (NoAbs x t) = NoAbs x $ substs us t
    substUnder n u (Abs   x t) = Abs   x $ substUnder (n + 1) u t
    substUnder n u (NoAbs x t) = NoAbs x $ substUnder n u t

instance Subst a => Subst (Arg a) where
    substs us      = fmap (substs us)
    substUnder n u = fmap (substUnder n u)

instance Subst a => Subst (Dom a) where
    substs us      = fmap (substs us)
    substUnder n u = fmap (substUnder n u)

instance Subst a => Subst (Maybe a) where
  substs us      = fmap (substs us)
  substUnder n u = fmap (substUnder n u)

instance Subst a => Subst [a] where
    substs us      = map (substs us)
    substUnder n u = map (substUnder n u)

instance (Subst a, Subst b) => Subst (a,b) where
    substs us (x,y)      = (substs us x, substs us y)
    substUnder n u (x,y) = (substUnder n u x, substUnder n u y)

instance Subst ClauseBody where
    substs us (Body t)        = Body $ substs us t
    substs us (Bind b)        = Bind $ substs us b
    substs _   NoBody         = NoBody
    substUnder n u (Body t)   = Body $ substUnder n u t
    substUnder n u (Bind b)   = Bind $ substUnder n u b
    substUnder _ _   NoBody   = NoBody

-- | Add @k@ to index of each open variable in @x@.
class Raise t where
    raiseFrom :: Nat -> Nat -> t -> t
    renameFrom :: Nat -> (Nat -> Nat) -> t -> t

instance Raise () where
  raiseFrom  _ _ _ = ()
  renameFrom _ _ _ = ()

instance Raise Nat where
    raiseFrom  m k i | i < m     = i
                     | otherwise = i + k
    renameFrom m k i | i < m     = i
                     | otherwise = k (i - m) + m

instance Raise a => Raise (Ptr a) where
  raiseFrom m k  = fmap (raiseFrom m k)
  renameFrom m k = fmap (renameFrom m k)

instance Raise Term where
    raiseFrom m k v =
        case v of
            Var i vs        -> Var (rf i) (rf vs)
{-
            Var i vs
                | i < m     -> Var i $ rf vs
                | otherwise -> Var (i + k) $ rf vs
-}
            Lam h m         -> Lam h $ rf m
            Def c vs        -> Def c $ rf vs
            Con c vs        -> Con c $ rf vs
            MetaV x vs      -> MetaV x $ rf vs
            Level l         -> Level $ rf l
            Lit l           -> Lit l
            Pi a b          -> uncurry Pi $ rf (a,b)
            Sort s          -> Sort $ rf s
            Shared p        -> Shared $ rf p
            DontCare mv     -> DontCare $ rf mv
        where
            rf x = raiseFrom m k x

    renameFrom m k v =
        case v of
            Var i vs        -> Var (rf i) (rf vs)
{-
            Var i vs
                | i < m     -> Var i $ rf vs
                | otherwise -> Var (k (i - m) + m) $ rf vs
-}
            Lam h m         -> Lam h $ rf m
            Def c vs        -> Def c $ rf vs
            Con c vs        -> Con c $ rf vs
            MetaV x vs      -> MetaV x $ rf vs
            Level l         -> Level $ rf l
            Lit l           -> Lit l
            Pi a b          -> uncurry Pi $ rf (a,b)
            Sort s          -> Sort $ rf s
            Shared p        -> Shared $ rf p
            DontCare mv     -> DontCare $ rf mv
        where
            rf x = renameFrom m k x

instance Raise Type where
    raiseFrom m k (El s t) = raiseFrom m k s `El` raiseFrom m k t
    renameFrom m k (El s t) = renameFrom m k s `El` renameFrom m k t

instance Raise Sort where
    raiseFrom m k s = case s of
      Type n     -> Type $ rf n
      Prop       -> Prop
      Inf        -> Inf
      DLub s1 s2 -> DLub (rf s1) (rf s2)
      where rf x = raiseFrom m k x

    renameFrom m k s = case s of
      Type n     -> Type $ rf n
      Prop       -> Prop
      Inf        -> Inf
      DLub s1 s2 -> DLub (rf s1) (rf s2)
      where rf x = renameFrom m k x

instance Raise Level where
  raiseFrom m k (Max as) = Max $ raiseFrom m k as
  renameFrom m k (Max as) = Max $ renameFrom m k as

instance Raise PlusLevel where
  raiseFrom m k l@ClosedLevel{} = l
  raiseFrom m k (Plus n l) = Plus n $ raiseFrom m k l
  renameFrom m k l@ClosedLevel{} = l
  renameFrom m k (Plus n l) = Plus n $ renameFrom m k l

instance Raise LevelAtom where
  raiseFrom m k l = case l of
    MetaLevel n vs   -> MetaLevel n $ raiseFrom m k vs
    NeutralLevel v   -> NeutralLevel $ raiseFrom m k v
    BlockedLevel n v -> BlockedLevel n $ raiseFrom m k v
    UnreducedLevel v -> UnreducedLevel $ raiseFrom m k v
  renameFrom m k l = case l of
    MetaLevel n vs   -> MetaLevel n $ renameFrom m k vs
    NeutralLevel v   -> NeutralLevel $ renameFrom m k v
    BlockedLevel n v -> BlockedLevel n $ renameFrom m k v
    UnreducedLevel v -> UnreducedLevel $ renameFrom m k v

instance Raise Constraint where
  raiseFrom m k c = case c of
    ValueCmp cmp a u v       -> ValueCmp cmp (rf a) (rf u) (rf v)
    ElimCmp ps a v e1 e2     -> ElimCmp ps (rf a) (rf v) (rf e1) (rf e2)
    TypeCmp cmp a b          -> TypeCmp cmp (rf a) (rf b)
    TelCmp a b cmp tel1 tel2 -> TelCmp (rf a) (rf b) cmp (rf tel1) (rf tel2)
    SortCmp cmp s1 s2        -> SortCmp cmp (rf s1) (rf s2)
    LevelCmp cmp l1 l2       -> LevelCmp cmp (rf l1) (rf l2)
    Guarded c cs             -> Guarded (rf c) cs
    IsEmpty r a              -> IsEmpty r (rf a)
    FindInScope m cands      -> FindInScope m (map rf cands)
    UnBlock{}                -> c
    where
      rf x = raiseFrom m k x
  renameFrom m k c = case c of
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
      rf x = renameFrom m k x

instance Raise Elim where
  raiseFrom m k e = case e of
    Apply v -> Apply (raiseFrom m k v)
    Proj{}  -> e
  renameFrom m k e = case e of
    Apply v -> Apply (renameFrom m k v)
    Proj{}  -> e

instance Raise ClauseBody where
  raiseFrom m k b = case b of
    Body v   -> Body $ rf v
    NoBody   -> NoBody
    Bind b   -> Bind $ rf b
    where rf x = raiseFrom m k x
  renameFrom m k b = case b of
    Body v   -> Body $ rf v
    NoBody   -> NoBody
    Bind b   -> Bind $ rf b
    where rf x = renameFrom m k x

-- Andreas, 2010-09-09 raise dot patterns and type info embedded in a pattern
instance Raise Pattern where
    raiseFrom m k p = case p of
      DotP t -> DotP $ raiseFrom m k t
      ConP c mt ps -> ConP c (raiseFrom m k mt) (raiseFrom m k ps)
      VarP x -> p
      LitP l -> p
    renameFrom m k p = case p of
      DotP t -> DotP $ renameFrom m k t
      ConP c mt ps -> ConP c (renameFrom m k mt) (renameFrom m k ps)
      VarP x -> p
      LitP l -> p

instance Raise a => Raise (Tele a) where
    raiseFrom m k EmptyTel          = EmptyTel
    raiseFrom m k (ExtendTel a tel) = uncurry ExtendTel $ raiseFrom m k (a, tel)
    renameFrom m k EmptyTel          = EmptyTel
    renameFrom m k (ExtendTel a tel) = uncurry ExtendTel $ renameFrom m k (a, tel)

instance Raise DisplayForm where
  raiseFrom m k (Display n ps v) = Display n (raiseFrom (m + 1) k ps)
                                             (raiseFrom (m + n) k v)
  renameFrom m k (Display n ps v) = Display n (renameFrom (m + 1) k ps)
                                             (renameFrom (m + n) k v)

instance Raise DisplayTerm where
  raiseFrom m k (DWithApp xs ys) = uncurry DWithApp $ raiseFrom m k (xs, ys)
  raiseFrom m k (DTerm v)        = DTerm $ raiseFrom m k v
  raiseFrom m k (DDot  v)        = DDot  $ raiseFrom m k v
  raiseFrom m k (DCon c vs)      = DCon c $ raiseFrom m k vs
  raiseFrom m k (DDef c vs)      = DDef c $ raiseFrom m k vs
  renameFrom m k (DWithApp xs ys) = uncurry DWithApp $ renameFrom m k (xs, ys)
  renameFrom m k (DTerm v)        = DTerm $ renameFrom m k v
  renameFrom m k (DDot  v)        = DDot  $ renameFrom m k v
  renameFrom m k (DCon c vs)      = DCon c $ renameFrom m k vs
  renameFrom m k (DDef c vs)      = DDef c $ renameFrom m k vs

instance Raise t => Raise (Abs t) where
    raiseFrom m k (Abs x v)   = Abs x $ raiseFrom (m + 1) k v
    raiseFrom m k (NoAbs x v) = NoAbs x $ raiseFrom m k v
    renameFrom m k (Abs x v)   = Abs x $ renameFrom (m + 1) k v
    renameFrom m k (NoAbs x v) = NoAbs x $ renameFrom m k v

instance Raise t => Raise (Arg t) where
    raiseFrom m k = fmap (raiseFrom m k)
    renameFrom m k = fmap (renameFrom m k)

instance Raise t => Raise (Dom t) where
    raiseFrom m k = fmap (raiseFrom m k)
    renameFrom m k = fmap (renameFrom m k)

instance Raise t => Raise (Blocked t) where
    raiseFrom m k = fmap (raiseFrom m k)
    renameFrom m k = fmap (renameFrom m k)

instance Raise t => Raise [t] where
    raiseFrom m k = fmap (raiseFrom m k)
    renameFrom m k = fmap (renameFrom m k)

instance Raise t => Raise (Maybe t) where
    raiseFrom m k = fmap (raiseFrom m k)
    renameFrom m k = fmap (renameFrom m k)

instance Raise v => Raise (Map k v) where
    raiseFrom m k = fmap (raiseFrom m k)
    renameFrom m k = fmap (renameFrom m k)

instance (Raise a, Raise b) => Raise (a,b) where
    raiseFrom m k (x,y) = (raiseFrom m k x, raiseFrom m k y)
    renameFrom m k (x,y) = (renameFrom m k x, renameFrom m k y)

raise :: Raise t => Nat -> t -> t
raise = raiseFrom 0

rename :: Raise t => (Nat -> Nat) -> t -> t
rename = renameFrom 0

data TelV a = TelV (Tele (Dom a)) a
  deriving (Typeable, Show, Eq, Ord, Functor)

type TelView = TelV Type
-- data TelView = TelV Telescope Type

telFromList :: [Dom (String, Type)] -> Telescope
telFromList = foldr (\(Dom h r (x, a)) -> ExtendTel (Dom h r a) . Abs x) EmptyTel

telToList :: Telescope -> [Dom (String, Type)]
telToList EmptyTel = []
telToList (ExtendTel arg tel) = fmap ((,) $ absName tel) arg : telToList (absBody tel)

telView' :: Type -> TelView
telView' t = case ignoreSharing $ unEl t of
  Pi a b  -> absV a (absName b) $ telView' (absBody b)
  _       -> TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

-- | @mkPi dom t = telePi (telFromList [dom]) t@
mkPi :: Dom (String, Type) -> Type -> Type
mkPi (Dom h r (x, a)) b = el $ Pi (Dom h r a) (mkAbs x b)
  where
    el = El $ dLub (getSort a) (Abs x (getSort b)) -- dLub checks x freeIn

telePi :: Telescope -> Type -> Type
telePi  EmptyTel         t = t
telePi (ExtendTel u tel) t = el $ Pi u (reAbs b)
  where
    el = El (dLub s1 s2)
    b = fmap (flip telePi t) tel
    s1 = getSort $ unDom u
    s2 = fmap getSort b

-- | Everything will be a pi.
telePi_ :: Telescope -> Type -> Type
telePi_  EmptyTel        t = t
telePi_ (ExtendTel u tel) t = el $ Pi u b
  where
    el = El (dLub s1 s2)
    b  = fmap (flip telePi_ t) tel
    s1 = getSort $ unDom u
    s2 = fmap getSort b

teleLam :: Telescope -> Term -> Term
teleLam  EmptyTel	  t = t
teleLam (ExtendTel u tel) t = Lam (domHiding u) $ flip teleLam t <$> tel

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
  Free.Unused   -> sLub s1 (absApp b __IMPOSSIBLE__)
  StronglyRigid -> Inf
  WeaklyRigid   -> Inf

-- Functions on abstractions ----------------------------------------------
--   and things we couldn't do before we could define 'absBody'

-- | Instantiate an abstraction
absApp :: Subst t => Abs t -> Term -> t
absApp (Abs   _ v) u = subst u v
absApp (NoAbs _ v) _ = v

absBody :: Raise t => Abs t -> t
absBody (Abs   _ v) = v
absBody (NoAbs _ v) = raise 1 v

mkAbs :: (Raise a, Free a) => String -> a -> Abs a
mkAbs x v | 0 `freeIn` v = Abs x v
          | otherwise    = NoAbs x (raise (-1) v)

reAbs :: (Raise a, Free a) => Abs a -> Abs a
reAbs (NoAbs x v) = NoAbs x v
reAbs (Abs x v)   = mkAbs x v

deriving instance (Raise a, Eq a) => Eq (Tele a)
deriving instance (Raise a, Ord a) => Ord (Tele a)

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

instance (Raise a, Eq a) => Eq (Abs a) where
  NoAbs _ a == NoAbs _ b = a == b
  Abs   _ a == Abs   _ b = a == b
  a         == b         = absBody a == absBody b

instance (Raise a, Ord a) => Ord (Abs a) where
  NoAbs _ a `compare` NoAbs _ b = a `compare` b
  Abs   _ a `compare` Abs   _ b = a `compare` b
  a         `compare` b         = absBody a `compare` absBody b

-- Level stuff ------------------------------------------------------------

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

unLevelAtom (MetaLevel x vs)   = MetaV x vs
unLevelAtom (NeutralLevel v)   = v
unLevelAtom (UnreducedLevel v) = v
unLevelAtom (BlockedLevel _ v) = v
