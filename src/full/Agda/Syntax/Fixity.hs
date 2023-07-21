{-# OPTIONS_GHC -Wunused-imports #-}

{-| Definitions for fixity, precedence levels, and declared syntax.
-}
module Agda.Syntax.Fixity where

import Control.DeepSeq

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Common

import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible

-- The Fixity data type is now defined in Agda.Syntax.Common.
-- Andreas, 2019-08-16, issue #1346

-- | Decorating something with @Fixity'@.
data ThingWithFixity x = ThingWithFixity x Fixity'
  deriving (Functor, Foldable, Traversable, Show)

instance LensFixity' (ThingWithFixity a) where
  lensFixity' f (ThingWithFixity a fix') = ThingWithFixity a <$> f fix'

instance LensFixity (ThingWithFixity a) where
  lensFixity = lensFixity' . lensFixity

-- | Do we prefer parens around arguments like @λ x → x@ or not?
--   See 'lamBrackets'.
data ParenPreference = PreferParen | PreferParenless
  deriving (Eq, Ord, Show, Generic)

instance NFData ParenPreference

preferParen :: ParenPreference -> Bool
preferParen p = PreferParen == p

preferParenless :: ParenPreference -> Bool
preferParenless p = PreferParenless == p

-- * Precendence

-- | Precedence is associated with a context.
data Precedence = TopCtx | FunctionSpaceDomainCtx
                | LeftOperandCtx Fixity | RightOperandCtx Fixity ParenPreference
                | FunctionCtx | ArgumentCtx ParenPreference | InsideOperandCtx
                | WithFunCtx | WithArgCtx | DotPatternCtx
    deriving (Show, Eq, Generic)

instance NFData Precedence

instance Pretty Precedence where
  pretty = text . show

-- | When printing we keep track of a stack of precedences in order to be able
--   to decide whether it's safe to leave out parens around lambdas. An empty
--   stack is equivalent to `TopCtx`. Invariant: `notElem TopCtx`.
type PrecedenceStack = [Precedence]

pushPrecedence :: Precedence -> PrecedenceStack -> PrecedenceStack
pushPrecedence TopCtx _  = []
pushPrecedence p      ps = p : ps

headPrecedence :: PrecedenceStack -> Precedence
headPrecedence []      = TopCtx
headPrecedence (p : _) = p

-- | Argument context preferring parens.
argumentCtx_ :: Precedence
argumentCtx_ = ArgumentCtx PreferParen

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets :: Fixity -> PrecedenceStack -> Bool
opBrackets = opBrackets' False

-- | Do we need to bracket an operator application of the given fixity
--   in a context with the given precedence.
opBrackets' :: Bool ->   -- Is the last argument a parenless lambda?
               Fixity -> PrecedenceStack -> Bool
opBrackets' isLam f ps = brack f (headPrecedence ps)
  where
    false = isLam && lamBrackets ps -- require more parens for `e >>= λ x → e₁` than `e >>= e₁`
    brack                        (Fixity _ (Related n1) LeftAssoc)
               (LeftOperandCtx   (Fixity _ (Related n2) LeftAssoc))  | n1 >= n2 = false
    brack                        (Fixity _ (Related n1) RightAssoc)
               (RightOperandCtx  (Fixity _ (Related n2) RightAssoc) _) | n1 >= n2 = false
    brack f1   (LeftOperandCtx  f2) | Related f1 <- fixityLevel f1
                                    , Related f2 <- fixityLevel f2
                                    , f1 > f2 = false
    brack f1   (RightOperandCtx f2 _) | Related f1 <- fixityLevel f1
                                    , Related f2 <- fixityLevel f2
                                    , f1 > f2 = false
    brack _ TopCtx                 = false
    brack _ FunctionSpaceDomainCtx = false
    brack _ InsideOperandCtx       = false
    brack _ WithArgCtx             = false
    brack _ WithFunCtx             = false
    brack _ _                      = True

-- | Does a lambda-like thing (lambda, let or pi) need brackets in the
-- given context? A peculiar thing with lambdas is that they don't
-- need brackets in certain right operand contexts. To decide we need to look
-- at the stack of precedences and not just the current precedence.
-- Example: @m₁ >>= (λ x → x) >>= m₂@ (for @_>>=_@ left associative).
lamBrackets :: PrecedenceStack -> Bool
lamBrackets []       = False
lamBrackets (p : ps) = case p of
  TopCtx                 -> __IMPOSSIBLE__
  ArgumentCtx pref       -> preferParen pref || lamBrackets ps
  RightOperandCtx _ pref -> preferParen pref || lamBrackets ps
  FunctionSpaceDomainCtx -> True
  LeftOperandCtx{}       -> True
  FunctionCtx            -> True
  InsideOperandCtx       -> True
  WithFunCtx             -> True
  WithArgCtx             -> True
  DotPatternCtx          -> True

-- | Does a function application need brackets?
appBrackets :: PrecedenceStack -> Bool
appBrackets = appBrackets' False

-- | Does a function application need brackets?
appBrackets' :: Bool ->   -- Is the argument of the application a parenless lambda?
                PrecedenceStack -> Bool
appBrackets' isLam ps = brack (headPrecedence ps)
  where
    brack ArgumentCtx{} = True
    brack DotPatternCtx = True
    brack _             = isLam && lamBrackets ps -- allow e + e₁ λ x → e₂

-- | Does a with application need brackets?
withAppBrackets :: PrecedenceStack -> Bool
withAppBrackets = brack . headPrecedence
  where
    brack TopCtx                 = False
    brack FunctionSpaceDomainCtx = False
    brack WithFunCtx             = False
    brack _                      = True

-- | Does a function space need brackets?
piBrackets :: PrecedenceStack -> Bool
piBrackets [] = False
piBrackets _  = True

roundFixBrackets :: PrecedenceStack -> Bool
roundFixBrackets ps = DotPatternCtx == headPrecedence ps

instance KillRange x => KillRange (ThingWithFixity x) where
  killRange (ThingWithFixity c f) = ThingWithFixity (killRange c) f
