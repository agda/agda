module Impl.LazyScope (LazyScope) where

import Prelude                                    hiding (pi, abs, foldr)

import           Bound                            hiding (instantiate)
import           Prelude.Extras                   (Eq1)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Control.Monad                    (ap)
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Monoid                      ((<>), mempty, mconcat)
import           Data.Typeable                    (Typeable)

import           Types.Term
import           Types.Var

-- Base terms
------------------------------------------------------------------------

newtype LazyScope v = LS {unLS :: TermView LazyScope v}
    deriving (Eq, Eq1, Functor, Foldable, Traversable, Typeable)

instance Monad LazyScope where
    return v = LS (App (Var v) [])

    LS term0 >>= f = LS $ case term0 of
        Lam body           -> Lam (LSAbs (unLSAbs body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (LSAbs (unLSAbs codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        Con n elims        -> Con n (map (>>= f) elims)
        Refl               -> Refl
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unLS $ eliminate (f v) elims'
                   Def n   -> App (Def n)   elims'
                   J       -> App J         elims'
                   Meta mv -> App (Meta mv) elims'

instance Applicative LazyScope where
    pure = return
    (<*>) = ap

instance MetaVars LazyScope where
    metaVars t = case view t of
        Lam body           -> metaVars $ unscope $ unLSAbs $ body
        Pi domain codomain -> metaVars domain <> metaVars (unscope (unLSAbs (codomain)))
        Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
        App h elims        -> metaVars h <> mconcat (map metaVars elims)
        Set                -> mempty
        Refl               -> mempty
        Con _ args         -> mconcat (map metaVars args)

instance HasAbs LazyScope where
    newtype Abs LazyScope v = LSAbs {unLSAbs :: Scope (Named ()) LazyScope v}

    toAbs   = LSAbs . toScope
    fromAbs = fromScope . unLSAbs

    weaken = LSAbs . Scope .  return . F

    instantiate abs t = instantiate1 t (unLSAbs abs)

    abstract v = LSAbs . Bound.abstract f
      where
        f v' = if v == v' then Just (named (varName v) ()) else Nothing

instance View LazyScope where
    unview = LS
    view   = unLS

instance Whnf LazyScope

instance IsTerm LazyScope

deriving instance Eq1 (Abs LazyScope)

deriving instance Functor (Abs LazyScope)

deriving instance Foldable (Abs LazyScope)

deriving instance Traversable (Abs LazyScope)
