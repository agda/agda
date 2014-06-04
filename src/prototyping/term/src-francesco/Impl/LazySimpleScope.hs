module Impl.LazySimpleScope (LazySimpleScope) where

import Prelude                                    hiding (pi, abs, foldr)

import           Bound.Class
import           Bound.Scope.Simple               hiding (instantiate)
import qualified Bound.Scope.Simple               as Bound
import           Prelude.Extras                   (Eq1)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Control.Monad                    (ap)
import           Control.Applicative              (Applicative(pure, (<*>)))
import           Data.Monoid                      ((<>), mempty, mconcat)
import           Data.Typeable                    (Typeable)

import           Types.Term
import           Types.Var
import           Eval

-- Base terms
------------------------------------------------------------------------

newtype LazySimpleScope v = LSS {unLSS :: TermView LazySimpleScope v}
    deriving (Eq, Eq1, Functor, Foldable, Traversable, Typeable)

instance Monad LazySimpleScope where
    return v = LSS (App (Var v) [])

    LSS term0 >>= f = LSS $ case term0 of
        Lam body           -> Lam (LSSAbs (unLSSAbs body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (LSSAbs (unLSSAbs codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        Con n elims        -> Con n (map (>>= f) elims)
        Refl               -> Refl
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unLSS $ eliminate (f v) elims'
                   Def n   -> App (Def n)   elims'
                   J       -> App J         elims'
                   Meta mv -> App (Meta mv) elims'

instance Applicative LazySimpleScope where
    pure = return
    (<*>) = ap

instance MetaVars LazySimpleScope where
    metaVars t = case view t of
        Lam body           -> metaVars $ unscope $ unLSSAbs $ body
        Pi domain codomain -> metaVars domain <> metaVars (unscope (unLSSAbs (codomain)))
        Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
        App h elims        -> metaVars h <> mconcat (map metaVars elims)
        Set                -> mempty
        Refl               -> mempty
        Con _ args         -> mconcat (map metaVars args)

instance HasAbs LazySimpleScope where
    newtype Abs LazySimpleScope v = LSSAbs {unLSSAbs :: Scope (Named ()) LazySimpleScope v}

    toAbs   = LSSAbs . toScope
    fromAbs = fromScope . unLSSAbs

    instantiate abs t = instantiate1 t (unLSSAbs abs)

    abstract v = LSSAbs . Bound.abstract f
      where
        f v' = if v == v' then Just (named (varName v) ()) else Nothing

instance View LazySimpleScope where
    unview = LSS
    view   = unLSS

instance IsTerm LazySimpleScope

deriving instance Eq1 (Abs LazySimpleScope)
deriving instance Functor (Abs LazySimpleScope)
deriving instance Foldable (Abs LazySimpleScope)
deriving instance Traversable (Abs LazySimpleScope)
