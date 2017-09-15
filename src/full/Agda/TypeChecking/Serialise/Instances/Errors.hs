{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}
{-# OPTIONS_GHC -fno-warn-orphans     #-}

#if __GLASGOW_HASKELL__ <= 708
{-# OPTIONS_GHC -fcontext-stack=30 #-}
#endif

module Agda.TypeChecking.Serialise.Instances.Errors where

#if __GLASGOW_HASKELL__ <= 708
import Agda.TypeChecking.Pretty ()
#endif

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common
import Agda.TypeChecking.Serialise.Instances.Internal ()
import Agda.TypeChecking.Serialise.Instances.Abstract ()

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Definitions (DeclarationWarning(..))
import Agda.Syntax.Abstract.Name (ModuleName)
import Agda.TypeChecking.Monad.Base
import Agda.Interaction.Options
import Agda.Termination.CutOff
import Agda.TypeChecking.Positivity.Occurrence ()
import Agda.Syntax.Parser.Monad (ParseWarning( OverlappingTokensWarning ))
import Agda.Utils.Pretty
import Agda.Utils.FileName ()

import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

instance EmbPrj TCWarning where
  icod_ (TCWarning a b c) = icodeN' TCWarning a b c

  value = valueN TCWarning

-- We don't need to serialise warnings that turn into errors
instance EmbPrj Warning where
  icod_ (TerminationIssue a)         = __IMPOSSIBLE__
  icod_ (UnreachableClauses a b)     = icodeN 0 UnreachableClauses a b
  icod_ (CoverageIssue a b)          = __IMPOSSIBLE__
  icod_ (CoverageNoExactSplit a b)   = __IMPOSSIBLE__
  icod_ (NotStrictlyPositive a b)    = __IMPOSSIBLE__
  icod_ (UnsolvedMetaVariables a)    = __IMPOSSIBLE__
  icod_ (UnsolvedInteractionMetas a) = __IMPOSSIBLE__
  icod_ (UnsolvedConstraints a)      = __IMPOSSIBLE__
  icod_ (OldBuiltin a b)             = icodeN 1 OldBuiltin a b
  icod_ EmptyRewritePragma           = icodeN 2 EmptyRewritePragma
  icod_ UselessPublic                = icodeN 3 UselessPublic
  icod_ (UselessInline a)            = icodeN 4 UselessInline a
  icod_ (GenericWarning a)           = icodeN 5 GenericWarning a
  icod_ (GenericNonFatalError a)     = __IMPOSSIBLE__
  icod_ (SafeFlagPostulate a)        = __IMPOSSIBLE__
  icod_ (SafeFlagPragma a)           = __IMPOSSIBLE__
  icod_ SafeFlagNonTerminating       = __IMPOSSIBLE__
  icod_ SafeFlagTerminating          = __IMPOSSIBLE__
  icod_ SafeFlagPrimTrustMe          = __IMPOSSIBLE__
  icod_ SafeFlagNoPositivityCheck    = __IMPOSSIBLE__
  icod_ SafeFlagPolarity             = __IMPOSSIBLE__
  icod_ (ParseWarning a)             = __IMPOSSIBLE__
  icod_ (DeprecationWarning a b c)   = icodeN 6 DeprecationWarning a b c
  icod_ (NicifierIssue a)            = icodeN 7 NicifierIssue a

  value = vcase valu where
      valu [0, a, b]    = valuN UnreachableClauses a b
      valu [1, a, b]    = valuN OldBuiltin a b
      valu [2]          = valuN EmptyRewritePragma
      valu [3]          = valuN UselessPublic
      valu [4, a]       = valuN UselessInline a
      valu [5, a]       = valuN GenericWarning a
      valu [6, a, b, c] = valuN DeprecationWarning a b c
      valu [7, a]       = valuN NicifierIssue a
      valu _ = malformed

instance EmbPrj DeclarationWarning where
  icod_ = \case
    UnknownNamesInFixityDecl a        -> icodeN 0 UnknownNamesInFixityDecl a
    UnknownNamesInPolarityPragmas a   -> icodeN 1 UnknownNamesInPolarityPragmas a
    PolarityPragmasButNotPostulates a -> icodeN 2 PolarityPragmasButNotPostulates a
    UselessPrivate a                  -> icodeN 3 UselessPrivate a
    UselessAbstract a                 -> icodeN 4 UselessAbstract a
    UselessInstance a                 -> icodeN 5 UselessInstance a
    EmptyMutual a                     -> icodeN 6 EmptyMutual a
    EmptyAbstract a                   -> icodeN 7 EmptyAbstract a
    EmptyPrivate a                    -> icodeN 8 EmptyPrivate a
    EmptyInstance a                   -> icodeN 9 EmptyInstance a
    EmptyMacro a                      -> icodeN 10 EmptyMacro a
    EmptyPostulate a                  -> icodeN 11 EmptyPostulate a

  value = vcase $ \case
    [0, a] -> valueN UnknownNamesInFixityDecl a
    [1, a] -> valueN UnknownNamesInPolarityPragmas a
    [2, a] -> valueN PolarityPragmasButNotPostulates a
    [3, a] -> valueN UselessPrivate a
    [4, a] -> valueN UselessAbstract a
    [5, a] -> valueN UselessInstance a
    [6, a] -> valueN EmptyMutual a
    [7, a] -> valueN EmptyAbstract a
    [8, a] -> valueN EmptyPrivate a
    [9, a] -> valueN EmptyInstance a
    [10,a] -> valueN EmptyMacro a
    [11,a] -> valueN EmptyPostulate a
    _ -> malformed

instance EmbPrj Doc where
  icod_ d = icodeN' (undefined :: String -> Doc) (render d)

  value = valueN text
