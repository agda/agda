{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS.Implicit where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad (forM)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Internal as I
import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Translation.InternalToAbstract (reify)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.TypeChecking.Rules.LHS.Problem

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

implicitP :: ArgInfo -> NamedArg A.Pattern
implicitP info = Arg (setOrigin Inserted info) $ unnamed $ A.WildP $ PatRange $ noRange

-- | Insert implicit patterns in a list of patterns.
--   Even if 'DontExpandLast', trailing SIZELT patterns are inserted.
insertImplicitPatterns :: ExpandHidden -> [NamedArg A.Pattern] ->
                          Telescope -> TCM [NamedArg A.Pattern]
insertImplicitPatterns exh ps tel =
  insertImplicitPatternsT exh ps (telePi tel typeDontCare)

-- | Insert trailing SizeLt patterns, if any.
insertImplicitSizeLtPatterns :: Type -> TCM [NamedArg A.Pattern]
insertImplicitSizeLtPatterns t = do
  -- Testing for SizeLt.  In case of blocked type, we return no.
  -- We assume that on the LHS, we know the type.  (TODO: Sufficient?)
  isSize <- isSizeTypeTest
  let isBounded BoundedNo   = False
      isBounded BoundedLt{} = True
      isSizeLt t = maybe False isBounded . isSize . unEl <$> reduce t

  -- Search for the last SizeLt type among the hidden arguments.
  TelV tel _ <- telView t
  let ts = reverse $ takeWhile (not . visible) $ telToList tel
  keep <- reverse <$> dropWhileM (not <.> isSizeLt . snd . unDom) ts
  -- Insert implicit patterns upto (including) the last SizeLt type.
  return [ implicitP ai | Dom ai _ <- keep ]

-- | Insert implicit patterns in a list of patterns.
--   Even if 'DontExpandLast', trailing SIZELT patterns are inserted.
insertImplicitPatternsT :: ExpandHidden -> [NamedArg A.Pattern] -> Type ->
                           TCM [NamedArg A.Pattern]
insertImplicitPatternsT DontExpandLast [] a = insertImplicitSizeLtPatterns a
insertImplicitPatternsT exh            ps a = do
  TelV tel b <- telViewUpTo' (-1) (not . visible) a
  reportSDoc "tc.lhs.imp" 20 $
    vcat [ text "insertImplicitPatternsT"
         , nest 2 $ text "ps  = " <+> do
             brackets $ fsep $ punctuate comma $ map prettyA ps
         , nest 2 $ text "tel = " <+> prettyTCM tel
         , nest 2 $ text "b   = " <+> addContext tel (prettyTCM b)
         ]
  case ps of
    [] -> insImp dummy tel
    p : ps -> do
      -- Andreas, 2015-05-11.
      -- If p is a projection pattern, make it visible for the purpose of
      -- calling insImp / insertImplicit, to get correct behavior.
      let p' = applyWhen (isJust $ A.maybePostfixProjP p) (setHiding NotHidden) p
      hs <- insImp p' tel
      case hs of
        [] -> do
          a <- reduce a
          case unEl a of
            Pi arg b -> do
              (p :) <$> insertImplicitPatternsT exh ps (absBody b)
            _ -> return (p : ps)
        hs -> insertImplicitPatternsT exh (hs ++ p : ps) (telePi tel b)
  where
    dummy = defaultNamedArg (A.VarP __IMPOSSIBLE__)

    insImp p EmptyTel = return []
    insImp p tel = case insertImplicit p $ map (argFromDom . fmap fst) $ telToList tel of
      BadImplicits   -> typeError WrongHidingInLHS
      NoSuchName x   -> typeError WrongHidingInLHS
      ImpInsert n    -> return $ map implicitArg n
      NoInsertNeeded -> return []

    implicitArg h = implicitP $ setHiding h $ defaultArgInfo
