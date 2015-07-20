{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}

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

-- | Insert implicit patterns in a problem.
insertImplicitProblem :: Problem -> TCM Problem
insertImplicitProblem (Problem ps qs tel pr) = do
  reportSDoc "tc.lhs.imp" 15 $
    sep [ text "insertImplicits"
        , nest 2 $ text "ps  = " <+> do brackets $ fsep $ punctuate comma $ map prettyA ps
        , nest 2 $ text "tel = " <+> prettyTCM tel
        ]
  ps' <- insertImplicitPatterns ExpandLast ps tel
  reportSDoc "tc.lhs.imp" 15 $
    sep [ text "insertImplicits finished"
        , nest 2 $ text "ps'  = " <+> do brackets $ fsep $ punctuate comma $ map prettyA ps'
        ]
  return $ Problem ps' qs tel pr

-- | Eta-expand implicit pattern if of record type.
expandImplicitPattern :: Type -> A.NamedArg A.Pattern -> TCM (A.NamedArg A.Pattern)
expandImplicitPattern a p = maybe (return p) return =<< expandImplicitPattern' a p

-- | Try to eta-expand implicit pattern.
--   Returns 'Nothing' unless dealing with a record type that has eta-expansion
--   and a constructor @c@.  In this case, it returns 'Just' @c _ _ ... _@
--   (record constructor applied to as many implicit patterns as there are fields).
expandImplicitPattern' :: Type -> A.NamedArg A.Pattern -> TCM (Maybe (A.NamedArg A.Pattern))
expandImplicitPattern' a p
  | A.WildP{} <- namedArg p, getHiding p /= Instance = do
     -- Eta expand implicit patterns of record type (issue 473),
     -- but not instance arguments since then they won't be found
     -- by the instance search
     caseMaybeM (isEtaRecordType =<< reduce a) (return Nothing) $ \ (d, _) -> do
       -- Andreas, 2012-06-10: only expand guarded records,
       -- otherwise we might run into an infinite loop
       def <- getRecordDef d
       -- Andreas, 2015-07-20 Since we have record patterns now, we can expand
       -- even records that do not have a constructor.
       -- -- Andreas, 2013-03-21: only expand records that have a constructor:
       -- if not (recNamedCon def) then return Nothing else do
       do
         -- generate one implicit pattern for each field
         qs <- forM (recFields def) $ \ f -> flip Arg implicitP <$> reify (argInfo f)
         -- generate the pattern (c _ _ ... _)
         let q  = A.ConP (ConPatInfo ConPImplicit patNoRange) (A.AmbQ [recCon def]) qs
         -- equip it with the name/arginfo of the original implicit pattern
             p' = updateNamedArg (const q) p   -- WAS: ((q <$) <$> p)  -- Andreas, 2013-03-21 forbiddingly cryptic
         return $ Just p'
  | otherwise = return Nothing

implicitP :: Named_ A.Pattern
implicitP = unnamed $ A.WildP $ PatRange $ noRange

-- | Insert implicit patterns in a list of patterns.
--   Even if 'DontExpandLast', trailing SIZELT patterns are inserted.
insertImplicitPatterns :: ExpandHidden -> [A.NamedArg A.Pattern] ->
                          Telescope -> TCM [A.NamedArg A.Pattern]
insertImplicitPatterns exh ps tel =
  insertImplicitPatternsT exh ps (telePi tel typeDontCare)

-- | Insert trailing SizeLt patterns, if any.
insertImplicitSizeLtPatterns :: Type -> TCM [A.NamedArg A.Pattern]
insertImplicitSizeLtPatterns t = do
  -- Testing for SizeLt.  In case of blocked type, we return no.
  -- We assume that on the LHS, we know the type.  (TODO: Sufficient?)
  isSize <- isSizeTypeTest
  let isBounded BoundedNo   = False
      isBounded BoundedLt{} = True
      isSizeLt t = maybe False isBounded . isSize <$> reduce t

  -- Search for the last SizeLt type among the hidden arguments.
  TelV tel _ <- telView t
  let ts = reverse $ takeWhile (not . visible) $ telToList tel
  keep <- reverse <$> dropWhileM (not <.> isSizeLt . snd . unDom) ts
  -- Insert implicit patterns upto (including) the last SizeLt type.
  forM keep $ \ (Dom ai _) -> flip Arg implicitP <$> reify ai

-- | Insert implicit patterns in a list of patterns.
--   Even if 'DontExpandLast', trailing SIZELT patterns are inserted.
insertImplicitPatternsT :: ExpandHidden -> [A.NamedArg A.Pattern] -> Type ->
                           TCM [A.NamedArg A.Pattern]
insertImplicitPatternsT DontExpandLast [] a = insertImplicitSizeLtPatterns a
insertImplicitPatternsT exh            ps a = do
  TelV tel b <- telViewUpTo' (-1) (not . visible) a
  reportSDoc "tc.lhs.imp" 20 $
    sep [ text "insertImplicitPatternsT"
        , nest 2 $ text "ps  = " <+> do
            brackets $ fsep $ punctuate comma $ map prettyA ps
        , nest 2 $ text "tel = " <+> prettyTCM tel
        , nest 2 $ text "b   = " <+> prettyTCM b
        ]
  case ps of
    [] -> do
      i <- insImp dummy tel
      case i of
        Just [] -> __IMPOSSIBLE__
        Just hs -> return hs
        Nothing -> return []
    p : ps -> do
      -- Andreas, 2015-05-11.
      -- If p is a projection pattern, make it visible for the purpose of
      -- calling insImp / insertImplicit, to get correct behavior.
      let p' = applyWhen (isJust $ isProjP p) (setHiding NotHidden) p
      i <- insImp p' tel
      case i of
        Just [] -> __IMPOSSIBLE__
        Just hs -> insertImplicitPatternsT exh (hs ++ p : ps) (telePi tel b)
        Nothing -> do
          a <- reduce a
          case ignoreSharing $ unEl a of
            Pi arg b -> do
              p <- expandImplicitPattern (unDom arg) p
              (p :) <$> insertImplicitPatternsT exh ps (absBody b)
            _ -> return (p : ps)
  where
    dummy = defaultNamedArg (A.VarP __IMPOSSIBLE__)

    insImp p EmptyTel
      | visible p          = return Nothing
      | isJust (isProjP p) = __IMPOSSIBLE__
      | otherwise          = typeError WrongHidingInLHS
    insImp p tel = case insertImplicit p $ map (argFromDom . fmap fst) $ telToList tel of
      BadImplicits   -> typeError WrongHidingInLHS
      NoSuchName x   -> typeError WrongHidingInLHS
      ImpInsert n    -> return $ Just (map implicitArg n)
      NoInsertNeeded -> return Nothing

    implicitArg h = setHiding h $ defaultArg implicitP
