{-# LANGUAGE TupleSections #-}

module Agda.Syntax.Abstract.Views where

import Control.Applicative
import Control.Monad.Identity
import Data.Traversable

import Agda.Syntax.Position
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Abstract
import Agda.Syntax.Info

data AppView = Application Expr [NamedArg Expr]
	     -- NonApplication Expr
	     --    -- ^ TODO: if we allow beta-redexes (which we currently do) there could be one here.
             -- 2011-08-24, Dominique: removed..

-- note: everything is an application, possibly of itself to 0 arguments
appView :: Expr -> AppView
appView e =
    case e of
      App i e1 arg        -> apply i (appView e1) arg
      ScopedExpr _ e      -> appView e
      _                   -> Application e []
    where
	apply i v arg =
	    case v of
		Application hd es -> Application hd $ es ++ [arg]

unAppView :: AppView -> Expr
unAppView (Application h es) =
  foldl (App (ExprRange noRange)) h es

-- | Check whether we are dealing with a universe.
isSet :: Expr -> Bool
isSet (ScopedExpr _ e) = isSet e
isSet (App _ e _)      = isSet e
isSet (Set{})          = True
isSet _                = False

-- | Remove top 'ScopedExpr' wrappers.
unScope :: Expr -> Expr
unScope (ScopedExpr scope e) = unScope e
unScope e                    = e

-- | Remove 'ScopedExpr' wrappers everywhere.
deepUnScope :: Expr -> Expr
deepUnScope = mapExpr unScope

-- * Traversal

-- | Apply an expression rewriting to every subexpression, inside-out.
--   See 'Agda.Syntax.Internal.Generic'
class ExprLike a where
  traverseExpr :: (Monad m, Applicative m) => (Expr -> m Expr) -> a -> m a
  mapExpr :: (Expr -> Expr) -> (a -> a)
  mapExpr f e = runIdentity $ traverseExpr (Identity . f) e

instance ExprLike Expr where
  traverseExpr f e = do
    let trav e = traverseExpr f e
    case e of
      Var{}                   -> f e
      Def{}                   -> f e
      Con{}                   -> f e
      Lit{}                   -> f e
      QuestionMark{}          -> f e
      Underscore{}            -> f e
      App ei e arg            -> f =<< App ei <$> trav e <*> trav arg
      WithApp ei e es         -> f =<< WithApp ei <$> trav e <*> trav es
      Lam ei b e              -> f =<< Lam ei <$> trav b <*> trav e
      AbsurdLam{}             -> f e
      ExtendedLam ei di x cls -> f =<< ExtendedLam ei di x <$> trav cls
      Pi ei tel e             -> f =<< Pi ei <$> trav tel <*> trav e
      Fun ei arg e            -> f =<< Fun ei <$> trav arg <*> trav e
      Set{}                   -> f e
      Prop{}                  -> f e
      Let ei bs e             -> f =<< Let ei <$> trav bs <*> trav e
      ETel tel                -> f =<< ETel <$> trav tel
      Rec ei bs               -> f =<< Rec ei <$> trav bs
      RecUpdate ei e bs       -> f =<< RecUpdate ei <$> trav e <*> trav bs
      ScopedExpr sc e         -> f =<< ScopedExpr sc <$> trav e
      QuoteGoal ei n e        -> f =<< QuoteGoal ei n <$> trav e
      Quote{}                 -> f e
      QuoteTerm{}             -> f e
      Unquote{}               -> f e
      DontCare e              -> f =<< DontCare <$> trav e
      PatternSyn{}            -> f e

-- | TODO: currently does not go into colors.
instance ExprLike a => ExprLike (Common.Arg c a) where
  traverseExpr = traverse . traverseExpr

instance ExprLike a => ExprLike (Named x a) where
  traverseExpr = traverse . traverseExpr

instance ExprLike a => ExprLike [a] where
  traverseExpr = traverse . traverseExpr

instance ExprLike a => ExprLike (x, a) where
  traverseExpr f (x, e) = (x,) <$> traverseExpr f e

instance ExprLike LamBinding where
  traverseExpr f e =
    case e of
      DomainFree{}  -> return e
      DomainFull bs -> DomainFull <$> traverseExpr f bs

instance ExprLike TypedBindings where
  traverseExpr f (TypedBindings r b) = TypedBindings r <$> traverseExpr f b

instance ExprLike TypedBinding where
  traverseExpr f e =
    case e of
      TBind r xs e -> TBind r xs <$> traverseExpr f e

instance ExprLike LetBinding where
  traverseExpr f e = do
    let trav e = traverseExpr f e
    case e of
      LetBind li ai x e e' -> LetBind li ai x <$> trav e <*> trav e'
      LetPatBind li p e    -> LetPatBind li <$> trav p <*> trav e
      LetApply{}           -> return e
      LetOpen{}            -> return e

-- | TODO: currently does not go into patterns.
instance ExprLike (Pattern' a) where
  traverseExpr f e = return e

-- | TODO: currently does not go into clauses.
instance ExprLike (Clause' a) where
  traverseExpr f e = return e
