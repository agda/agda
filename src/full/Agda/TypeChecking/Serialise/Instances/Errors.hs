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

  value = vcase valu where
      valu [0, a, b]     = valuN UnreachableClauses a b
      valu [1, a, b]     = valuN OldBuiltin a b
      valu [2]           = valuN EmptyRewritePragma
      valu [3]          = valuN UselessPublic
      valu [4, a]       = valuN UselessInline a
      valu [5, a]       = valuN GenericWarning a
      valu [6, a, b, c] = valuN DeprecationWarning a b c
      valu _             = malformed

instance EmbPrj Doc where
  icod_ d = icodeN' (undefined :: String -> Doc) (render d)

  value = valueN text

instance EmbPrj a => EmbPrj (Closure a) where
  icod_ (Closure a b c d e) = icodeN' Closure a b c d e

  value = valueN Closure


-- We are only serialising the parts of the environment and the state
-- that we need for displaying the warnings.
-- NOTE: If needed for other things, this might need to be changed!

instance EmbPrj TCEnv where
  icod_ TCEnv{..} = icodeN' (undefined :: ModuleName -> SerialisedRange -> TCEnv)
                            envCurrentModule (SerialisedRange envRange)

  value = valueN $ \ a c -> initEnv
                 { envCurrentModule = a
                 , envRange = underlyingRange c
                 , envCall = Nothing
                 }

instance EmbPrj TCState where
  icod_ st = icodeN' (undefined :: Signature -> ModuleToSource -> PragmaOptions
                                -> BuiltinThings PrimFun -> MetaStore
                                -> InteractionPoints -> Signature
                                -> BuiltinThings PrimFun -> TCState)
                     (st ^. stImports)
                     (st ^. stModuleToSource)
                     (st ^. stPragmaOptions)
                     (st ^. stImportedBuiltins)
                     (st ^. stMetaStore)
                     (st ^. stInteractionPoints)
                     (st ^. stSignature)
                     (st ^. stLocalBuiltins)

  value = valueN (\ a b c d e f g h ->
                     set stImports           a $
                     set stModuleToSource    b $
                     set stPragmaOptions     c $
                     set stImportedBuiltins  d $
                     set stMetaStore         e $
                     set stInteractionPoints f $
                     set stSignature         g $
                     set stLocalBuiltins     h $
                     initState)

instance EmbPrj InteractionId where
  icod_ (InteractionId a) = icodeN' InteractionId a

  value = valueN InteractionId

instance EmbPrj PragmaOptions where
  -- TODO: only keep the options needed for displaying the warnings
  icod_ (PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y) =
    icodeN' PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y

  value = valueN PragmaOptions

instance EmbPrj PrimFun where
  -- don't need implementation for the warnings
  icod_ (PrimFun a b r)= icodeN' (\ a b -> PrimFun a b r) a b

  value = valueN (\ a b -> PrimFun a b __IMPOSSIBLE__)

instance EmbPrj CutOff where
  icod_ (CutOff a) = icodeN 0 CutOff a
  icod_ DontCutOff = icodeN 1 DontCutOff

  value = vcase valu where
    valu [0, a] = valuN CutOff a
    valu [1]    = valuN DontCutOff
    valu _      = malformed

instance EmbPrj MetaVariable where
  icod_ (MetaVar a b c d r s t) = icodeN' (\ a b c d -> MetaVar a b c d r s t) a b c d

  value = valueN $ \ a b c d ->
          MetaVar a b c d __IMPOSSIBLE__ __IMPOSSIBLE__ __IMPOSSIBLE__

instance EmbPrj a => EmbPrj (Judgement a) where
  icod_ (HasType a b) = icodeN 0 HasType a b
  icod_ (IsSort a b)  = icodeN 1 IsSort a b

  value = vcase valu where
    valu [0, a, b] = valuN HasType a b
    valu [1, a, b] = valuN IsSort a b
    valu _         = malformed

instance EmbPrj MetaPriority where
  icod_ (MetaPriority a) = icodeN' MetaPriority a

  value = valueN MetaPriority

instance EmbPrj MetaInfo where
  icod_ (MetaInfo a b c) = icodeN' MetaInfo a b c

  value = valueN MetaInfo

instance EmbPrj RunMetaOccursCheck where
  icod_ RunMetaOccursCheck     = icodeN 0 RunMetaOccursCheck
  icod_ DontRunMetaOccursCheck = icodeN 1 DontRunMetaOccursCheck

  value = vcase valu where
    valu [0] = valuN RunMetaOccursCheck
    valu [1] = valuN DontRunMetaOccursCheck
    valu _   = malformed

instance EmbPrj InteractionPoint where
  icod_ (InteractionPoint a b c r) = icodeN' (\ a b c -> InteractionPoint a b c r) a b c

  value = valueN (\ a b c -> InteractionPoint a b c __IMPOSSIBLE__)

instance EmbPrj ModuleParameters where
  icod_ (ModuleParams a) = icodeN' ModuleParams a

  value = valueN ModuleParams

