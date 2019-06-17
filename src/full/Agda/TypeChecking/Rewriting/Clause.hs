{-# LANGUAGE TypeFamilies #-}

module Agda.TypeChecking.Rewriting.Clause where

import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Monad

------------------------------------------------------------------------
-- * Converting clauses to rewrite rules
------------------------------------------------------------------------

-- | Get all the clauses of a definition and convert them to rewrite
--   rules.
getClausesAsRewriteRules :: QName -> TCM [RewriteRule]
getClausesAsRewriteRules f = do
  cls <- defClauses <$> getConstInfo f
  forMaybeM (zip [1..] cls) $ \(i,cl) -> do
    clname <- clauseQName f i
    return $ clauseToRewriteRule f clname cl

-- | Generate a sensible name for the given clause
clauseQName :: QName -> Int -> TCM QName
clauseQName f i = QName (qnameModule f) <$> clauseName (qnameName f) i
  where
    clauseName n i = freshName noRange (show n ++ "-clause" ++ show i)

-- | @clauseToRewriteRule f q cl@ converts the clause @cl@ of the
--   function @f@ to a rewrite rule with name @q@. Returns @Nothing@
--   if @clauseBody cl@ is @Nothing@. Precondition: @clauseType cl@ is
--   not @Nothing@.
clauseToRewriteRule :: QName -> QName -> Clause -> Maybe RewriteRule
clauseToRewriteRule f q cl = clauseBody cl <&> \rhs -> RewriteRule
  { rewName    = q
  , rewContext = clauseTel cl
  , rewHead    = f
  , rewPats    = toNLPat $ namedClausePats cl
  , rewRHS     = rhs
  , rewType    = unArg $ fromMaybe __IMPOSSIBLE__  $ clauseType cl
  }

class ToNLPat a b where
  toNLPat :: a -> b

  default toNLPat
    :: ( ToNLPat a' b', Functor f, a ~ f a', b ~ f b')
    => a -> b
  toNLPat = fmap toNLPat

instance ToNLPat a b => ToNLPat [a] [b] where
instance ToNLPat a b => ToNLPat (Dom a) (Dom b) where
instance ToNLPat a b => ToNLPat (Elim' a) (Elim' b) where
instance ToNLPat a b => ToNLPat (Abs a) (Abs b) where

instance ToNLPat (Arg DeBruijnPattern) (Elim' NLPat) where
  toNLPat (Arg ai p) = case p of
    VarP _ x        -> app $ PVar (dbPatVarIndex x) []
    DotP _ u        -> app $ PTerm u
    ConP c _ ps     -> app $ PDef (conName c) $ toNLPat ps
    LitP l          -> app $ PTerm $ Lit l
    ProjP o f       -> Proj o f
    IApplyP _ u v x -> IApply (PTerm u) (PTerm v) $ PVar (dbPatVarIndex x) []
    DefP _ f ps     -> app $ PDef f $ toNLPat ps

    where
      app = Apply . Arg ai

instance ToNLPat (NamedArg DeBruijnPattern) (Elim' NLPat) where
  toNLPat = toNLPat . fmap namedThing
