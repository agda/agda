{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE CPP                      #-}
{-# OPTIONS_GHC -fno-warn-orphans     #-}

module Agda.TypeChecking.Serialise.Instances.Errors where

#if __GLASGOW_HASKELL__ <= 708
import Agda.TypeChecking.Pretty ()
#endif

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances.Common
import Agda.TypeChecking.Serialise.Instances.Internal ()
import Agda.TypeChecking.Serialise.Instances.Abstract ()

import Agda.Syntax.Common
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
  icod_ (TCWarning a b c) = icode3' a b c

  value = value3 TCWarning

-- We don't need to serialise warnings that turn into errors
instance EmbPrj Warning where
  icod_ (TerminationIssue a)         = __IMPOSSIBLE__
  icod_ (UnreachableClauses a b)     = icode2 0  a b
  icod_ (CoverageIssue a b)          = __IMPOSSIBLE__
  icod_ (CoverageNoExactSplit a b)   = __IMPOSSIBLE__
  icod_ (NotStrictlyPositive a b)    = __IMPOSSIBLE__
  icod_ (UnsolvedMetaVariables a)    = __IMPOSSIBLE__
  icod_ (UnsolvedInteractionMetas a) = __IMPOSSIBLE__
  icod_ (UnsolvedConstraints a)      = __IMPOSSIBLE__
  icod_ (OldBuiltin a b)             = icode1 1  a
  icod_ EmptyRewritePragma           = icode0 2
  icod_ UselessPublic                = icode0 3
  icod_ (UselessInline a)            = icode1 4 a
  icod_ (GenericWarning a)           = icode1 5 a
  icod_ (GenericNonFatalError a)     = __IMPOSSIBLE__
  icod_ (SafeFlagPostulate a)        = __IMPOSSIBLE__
  icod_ (SafeFlagPragma a)           = __IMPOSSIBLE__
  icod_ SafeFlagNonTerminating       = __IMPOSSIBLE__
  icod_ SafeFlagTerminating          = __IMPOSSIBLE__
  icod_ SafeFlagPrimTrustMe          = __IMPOSSIBLE__
  icod_ SafeFlagNoPositivityCheck    = __IMPOSSIBLE__
  icod_ SafeFlagPolarity             = __IMPOSSIBLE__
  icod_ (ParseWarning a)             = __IMPOSSIBLE__
  icod_ (DeprecationWarning a b c)   = icode3 6 a b c

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
  icod_ d = icode1' (render d)

  value = value1 text

instance EmbPrj a => EmbPrj (Closure a) where
  icod_ (Closure a b c d e) = icode5' a b c d e

  value = value5 Closure


-- We are only serialising the parts of the environment and the state
-- that we need for displaying the warnings.
-- NOTE: If needed for other things, this might need to be changed!

instance EmbPrj TCEnv where
  icod_ TCEnv{..} = icode2' envCurrentModule (SerialisedRange envRange)

  value = value2 $ \ a c -> initEnv
                 { envCurrentModule = a
                 , envRange = underlyingRange c
                 , envCall = Nothing
                 }

instance EmbPrj TCState where
  icod_ st = icode8' (st ^. stImports)
                     (st ^. stModuleToSource)
                     (st ^. stPragmaOptions)
                     (st ^. stImportedBuiltins)
                     (st ^. stMetaStore)
                     (st ^. stInteractionPoints)
                     (st ^. stSignature)
                     (st ^. stLocalBuiltins)

  value = value8 (\ a b c d e f g h ->
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
  icod_ (InteractionId a) = icode1' a

  value = value1 InteractionId

instance EmbPrj PragmaOptions where
  -- TODO: only keep the options needed for displaying the warnings
  icod_ (PragmaOptions a b c d e f g h i j k l m n o p q r s t u v w x y) = icode25' a b c d e f g h i j k l m n o p q r s t u v w x y

  value = value25 PragmaOptions

instance EmbPrj PrimFun where
  -- don't need implementation for the warnings
  icod_ (PrimFun a b _)= icode2' a b

  value = value2 (\ a b -> PrimFun a b __IMPOSSIBLE__)

instance EmbPrj CutOff where
  icod_ (CutOff a) = icode1 0 a
  icod_ DontCutOff = icode0 1

  value = vcase valu where
    valu [0, a] = valuN CutOff a
    valu [1]    = valuN DontCutOff
    valu _         = malformed

instance EmbPrj MetaVariable where
  icod_ (MetaVar a b c d _ _ _) = icode4' a b c d

  value = value4 $ \ a b c d ->
          MetaVar a b c d __IMPOSSIBLE__ __IMPOSSIBLE__ __IMPOSSIBLE__

instance EmbPrj a => EmbPrj (Judgement a) where
  icod_ (HasType a b) = icode2 0 a b
  icod_ (IsSort a b)  = icode2 1 a b

  value = vcase valu where
    valu [0, a, b] = valuN HasType a b
    valu [1, a, b] = valuN IsSort a b
    valu _         = malformed

instance EmbPrj MetaPriority where
  icod_ (MetaPriority a) = icode1' a

  value = value1 MetaPriority

instance EmbPrj MetaInfo where
  icod_ (MetaInfo a b c) = icode3' a b c

  value = value3 MetaInfo

instance EmbPrj RunMetaOccursCheck where
  icod_ RunMetaOccursCheck = icode0 0
  icod_ DontRunMetaOccursCheck = icode0 1

  value = vcase valu where
    valu [0] = valuN RunMetaOccursCheck
    valu [1] = valuN DontRunMetaOccursCheck
    valu _   = malformed

instance EmbPrj InteractionPoint where
  icod_ (InteractionPoint a b c _) = icode3' a b c

  value = value3 (\ a b c -> InteractionPoint a b c __IMPOSSIBLE__)

instance EmbPrj ModuleParameters where
  icod_ (ModuleParams a) = icode1' a

  value = value1 ModuleParams

