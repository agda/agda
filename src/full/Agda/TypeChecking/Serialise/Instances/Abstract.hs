{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Serialise.Instances.Abstract where

import Control.Applicative

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position as P
import Agda.Syntax.Fixity

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common ()

import Agda.TypeChecking.Monad

import Agda.Utils.Except

#include "undefined.h"
import Agda.Utils.Impossible

instance EmbPrj Scope where
  icod_ (Scope a b c d e) = icode5' a b c d e

  value = vcase valu where
    valu [a, b, c, d, e] = valu5 Scope a b c d e
    valu _               = malformed

instance EmbPrj NameSpaceId where
  icod_ PublicNS        = icode0'
  icod_ PrivateNS       = icode0 1
  icod_ ImportedNS      = icode0 2
  icod_ OnlyQualifiedNS = icode0 3

  value = vcase valu where
    valu []  = valu0 PublicNS
    valu [1] = valu0 PrivateNS
    valu [2] = valu0 ImportedNS
    valu [3] = valu0 OnlyQualifiedNS
    valu _   = malformed

instance EmbPrj Access where
  icod_ PrivateAccess = icode0 0
  icod_ PublicAccess  = icode0'
  icod_ OnlyQualified = icode0 2

  value = vcase valu where
    valu [0] = valu0 PrivateAccess
    valu []  = valu0 PublicAccess
    valu [2] = valu0 OnlyQualified
    valu _   = malformed

instance EmbPrj NameSpace where
  icod_ (NameSpace a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 NameSpace a b
    valu _      = malformed

instance EmbPrj WhyInScope where
  icod_ Defined       = icode0'
  icod_ (Opened a b)  = icode2 0 a b
  icod_ (Applied a b) = icode2 1 a b

  value = vcase valu where
    valu []        = valu0 Defined
    valu [0, a, b] = valu2 Opened a b
    valu [1, a, b] = valu2 Applied a b
    valu _         = malformed

instance EmbPrj AbstractName where
  icod_ (AbsName a b c) = icode3' a b c

  value = vcase valu where
    valu [a, b, c] = valu3 AbsName a b c
    valu _         = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 AbsModule a b
    valu _      = malformed

instance EmbPrj KindOfName where
  icod_ DefName        = icode0'
  icod_ ConName        = icode0 1
  icod_ FldName        = icode0 2
  icod_ PatternSynName = icode0 3
  icod_ QuotableName   = icode0 4

  value = vcase valu where
    valu []  = valu0 DefName
    valu [1] = valu0 ConName
    valu [2] = valu0 FldName
    valu [3] = valu0 PatternSynName
    valu [4] = valu0 QuotableName
    valu _   = malformed

instance EmbPrj LocalVar where
  icod_ (LocalVar a)      = icode1' a
  icod_ (ShadowedVar a b) = icode2' a b

  value = vcase valu where
    valu [a]    = valu1 LocalVar a
    valu [a, b] = valu2 ShadowedVar a b
    valu _      = malformed

-- Only used for pattern synonyms
instance EmbPrj A.Expr where
  icod_ (A.Var n)               = icode1 0 n
  icod_ (A.Def n)               = icode1 1 n
  icod_ (A.Con ns)              = icode1 2 ns
  icod_ (A.Lit l)               = icode1 3 l
  icod_ (A.QuestionMark{})      = icode0 4
  icod_ (A.Underscore _)        = icode0 5
  icod_ (A.App _ a b)           = icode2 6 a b
  icod_ (A.WithApp _ a b)       = icode2 7 a b
  icod_ (A.Lam  _ a b)          = icode2 8 a b
  icod_ (A.AbsurdLam _ a)       = icode1 9 a
  icod_ (A.ExtendedLam _ _ _ _) = __IMPOSSIBLE__
  icod_ (A.Pi   _ a b)          = icode2 11 a b
  icod_ (A.Fun  _ a b)          = icode2 12 a b
  icod_ (A.Set  _ a)            = icode1 13 a
  icod_ (A.Prop _)              = icode0 14
  icod_ (A.Let  _ _ _)          = __IMPOSSIBLE__
  icod_ (A.ETel{})              = __IMPOSSIBLE__
  icod_ (A.Rec  _ a)            = icode1 17 a
  icod_ (A.RecUpdate _ a b)     = icode2 18 a b
  -- Andreas, 2015-07-15, drop scopes embedded in expressions.
  -- As expressions are not @unScope@d before serialization,
  -- this case is not __IMPOSSIBLE__.
  icod_ (A.ScopedExpr a b)      = icod_ b -- WAS: icode2 19 a b
  icod_ (A.QuoteGoal _ a b)     = icode2 20 a b
  icod_ (A.QuoteContext _ a b)  = icode2 21 a b
  icod_ (A.Quote _)             = icode0 22
  icod_ (A.QuoteTerm _)         = icode0 23
  icod_ (A.Unquote _)           = icode0 24
  icod_ (A.DontCare a)          = icode1 25 a
  icod_ (A.PatternSyn a)        = icode1 26 a
  icod_ (A.Proj a)              = icode1 27 a

  value = vcase valu where
    valu [0, a]     = valu1 A.Var a
    valu [1, a]     = valu1 A.Def a
    valu [2, a]     = valu1 A.Con a
    valu [3, a]     = valu1 A.Lit a
    valu [4]        = valu0 (A.QuestionMark emptyMetaInfo 0)
    valu [5]        = valu0 (A.Underscore emptyMetaInfo)
    valu [6, a, b]  = valu2 (A.App i) a b
    valu [7, a, b]  = valu2 (A.WithApp i) a b
    valu [8, a, b]  = valu2 (A.Lam i) a b
    valu [9, a]     = valu1 (A.AbsurdLam i) a
    valu [11, a, b] = valu2 (A.Pi i) a b
    valu [12, a, b] = valu2 (A.Fun i) a b
    valu [13, a]    = valu1 (A.Set i) a
    valu [14]       = valu0 (A.Prop i)
    valu [17, a]    = valu1 (A.Rec i) a
    valu [18, a, b] = valu2 (A.RecUpdate i) a b
    -- valu [19, a, b] = valu2 A.ScopedExpr a b
    valu [20, a, b] = valu2 (A.QuoteGoal i) a b
    valu [21, a, b] = valu2 (A.QuoteContext i) a b
    valu [22]       = valu0 (A.Quote i)
    valu [23]       = valu0 (A.QuoteTerm i)
    valu [24]       = valu0 (A.Unquote i)
    valu [25, a]    = valu1 A.DontCare a
    valu [26, a]    = valu1 A.PatternSyn a
    valu [27, a]    = valu1 A.Proj a
    valu _          = malformed

    i = ExprRange noRange

instance EmbPrj ConPatInfo where
  icod_ (ConPatInfo a _) = icod_ a
  value a                = flip ConPatInfo patNoRange <$> value a

instance EmbPrj A.Pattern where
  icod_ (A.VarP a)            = icode1 0 a
  icod_ (A.ConP a b c)        = icode3 1 a b c
  icod_ (A.DefP _ a b)        = icode2 2 a b
  icod_ (A.WildP _)           = icode0 3
  icod_ (A.AsP _ a b)         = icode2 4 a b
  icod_ (A.DotP _ a)          = icode1 5 a
  icod_ (A.AbsurdP _)         = icode0 6
  icod_ (A.LitP a)            = icode1 7 a
  icod_ (A.PatternSynP _ a b) = icode2 9 a b

  value = vcase valu where
    valu [0, a]       = valu1 A.VarP a
    valu [1, a, b, c] = valu3 A.ConP a b c
    valu [2, a, b]    = valu2 (A.DefP i) a b
    valu [3]          = valu0 (A.WildP i)
    valu [4, a, b]    = valu2 (A.AsP i) a b
    valu [5, a]       = valu1 (A.DotP i) a
    valu [6]          = valu0 (A.AbsurdP i)
    valu [7, a]       = valu1 (A.LitP) a
    valu [9, a, b]    = valu2 (A.PatternSynP i) a b
    valu _            = malformed

    i = patNoRange

instance EmbPrj A.LamBinding where
  icod_ (A.DomainFree i e) = icode2 0 i e
  icod_ (A.DomainFull a)   = icode1 1 a

  value = vcase valu where
    valu [0, i, e] = valu2 A.DomainFree i e
    valu [1, a]    = valu1 A.DomainFull a
    valu _         = malformed

instance EmbPrj A.LetBinding where
  icod_ (A.LetBind _ a b c d)  = icode4 0 a b c d
  icod_ (A.LetPatBind _ a b )  = icode2 1 a b
  icod_ (A.LetApply _ _ _ _ _) = icode0 2
  icod_ (A.LetOpen _ _)        = icode0 2

  value = vcase valu where
    valu [0, a, b, c, d] = valu4 (A.LetBind (LetRange noRange)) a b c d
    valu [1, a, b]       = valu2 (A.LetPatBind (LetRange noRange)) a b
    valu [2]             = throwError $ NotSupported
                             "importing pattern synonym containing let module"
    valu _               = malformed

instance EmbPrj A.TypedBindings where
  icod_ (A.TypedBindings a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 A.TypedBindings a b
    valu _      = malformed

instance EmbPrj A.TypedBinding where
  icod_ (A.TBind a b c) = icode3 0 a b c
  icod_ (A.TLet a b)    = icode2 1 a b

  value = vcase valu where
    valu [0, a, b, c] = valu3 A.TBind a b c
    valu [1, a, b]    = valu2 A.TLet a b
    valu _            = malformed

instance EmbPrj Precedence where
  icod_ TopCtx                 = icode0'
  icod_ FunctionSpaceDomainCtx = icode0 1
  icod_ (LeftOperandCtx a)     = icode1 2 a
  icod_ (RightOperandCtx a)    = icode1 3 a
  icod_ FunctionCtx            = icode0 4
  icod_ ArgumentCtx            = icode0 5
  icod_ InsideOperandCtx       = icode0 6
  icod_ WithFunCtx             = icode0 7
  icod_ WithArgCtx             = icode0 8
  icod_ DotPatternCtx          = icode0 9

  value = vcase valu where
    valu []     = valu0 TopCtx
    valu [1]    = valu0 FunctionSpaceDomainCtx
    valu [2, a] = valu1 LeftOperandCtx a
    valu [3, a] = valu1 RightOperandCtx a
    valu [4]    = valu0 FunctionCtx
    valu [5]    = valu0 ArgumentCtx
    valu [6]    = valu0 InsideOperandCtx
    valu [7]    = valu0 WithFunCtx
    valu [8]    = valu0 WithArgCtx
    valu [9]    = valu0 DotPatternCtx
    valu _      = malformed

instance EmbPrj ScopeInfo where
  icod_ (ScopeInfo a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 ScopeInfo a b c d
    valu _            = malformed
