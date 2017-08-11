{-# LANGUAGE CPP #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module Agda.TypeChecking.Implicit where

import Control.Applicative
import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal as I

import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty

import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | @implicitArgs n expand eti t@ generates up to @n@ implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding info of its domain.
--
--   If explicit arguments are to be inserted as well, they are
--   inserted as instance arguments (used for recursive instance search).

implicitArgs :: Int -> (Hiding -> Bool) -> Type -> TCM (Args, Type)
implicitArgs n expand t = mapFst (map (fmap namedThing)) <$> do
  implicitNamedArgs n (\ h x -> expand h) t

-- | @implicitNamedArgs n expand eti t@ generates up to @n@ named implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding and name info of its domain.
--
--   If explicit arguments are to be inserted as well, they are
--   inserted as instance arguments (used for recursive instance search).

implicitNamedArgs :: Int -> (Hiding -> ArgName -> Bool) -> Type -> TCM (NamedArgs, Type)
implicitNamedArgs 0 expand t0 = return ([], t0)
implicitNamedArgs n expand t0 = do
    t0' <- reduce t0
    case ignoreSharing $ unEl t0' of
      Pi (Dom info a) b | let x = absName b, expand (getHiding info) x -> do
          info' <- if hidden info then return info else do
            reportSDoc "tc.term.args.ifs" 15 $
              text "inserting instance meta for type" <+> prettyTCM a
            return $ makeInstance info
          (_, v) <- newMetaArg info' x a
          let narg = Arg info (Named (Just $ unranged x) v)
          mapFst (narg :) <$> implicitNamedArgs (n-1) expand (absApp b v)
      _ -> return ([], t0')

-- | Create a metavariable according to the 'Hiding' info.

newMetaArg
  :: ArgInfo   -- ^ Kind/relevance of meta.
  -> ArgName   -- ^ Name suggestion for meta.
  -> Type      -- ^ Type of meta.
  -> TCM (MetaId, Term)  -- ^ The created meta as id and as term.
newMetaArg info x a = do
  applyRelevanceToContext (getRelevance info) $
    newMeta (getHiding info) (argNameToString x) a
  where
    newMeta :: Hiding -> String -> Type -> TCM (MetaId, Term)
    newMeta Instance{} = newIFSMeta
    newMeta Hidden     = newNamedValueMeta RunMetaOccursCheck
    newMeta NotHidden  = newNamedValueMeta RunMetaOccursCheck

-- | Create a questionmark according to the 'Hiding' info.

newInteractionMetaArg
  :: ArgInfo   -- ^ Kind/relevance of meta.
  -> ArgName   -- ^ Name suggestion for meta.
  -> Type      -- ^ Type of meta.
  -> TCM (MetaId, Term)  -- ^ The created meta as id and as term.
newInteractionMetaArg info x a = do
  applyRelevanceToContext (getRelevance info) $
    newMeta (getHiding info) (argNameToString x) a
  where
    newMeta :: Hiding -> String -> Type -> TCM (MetaId, Term)
    newMeta Instance{} = newIFSMeta
    newMeta Hidden     = newNamedValueMeta' DontRunMetaOccursCheck
    newMeta NotHidden  = newNamedValueMeta' DontRunMetaOccursCheck

---------------------------------------------------------------------------

data ImplicitInsertion
      = ImpInsert [Hiding]        -- ^ this many implicits have to be inserted
      | BadImplicits      -- ^ hidden argument where there should have been a non-hidden arg
      | NoSuchName ArgName -- ^ bad named argument
      | NoInsertNeeded
  deriving (Show)

impInsert :: [Hiding] -> ImplicitInsertion
impInsert [] = NoInsertNeeded
impInsert hs = ImpInsert hs

-- | The list should be non-empty.
insertImplicit :: NamedArg e -> [Arg ArgName] -> ImplicitInsertion
insertImplicit _ [] = __IMPOSSIBLE__
insertImplicit a ts | visible a = impInsert $ nofHidden ts
  where
    nofHidden :: [Arg a] -> [Hiding]
    nofHidden = takeWhile notVisible . map getHiding
insertImplicit a ts =
  case nameOf (unArg a) of
    Nothing -> maybe BadImplicits impInsert $ upto (getHiding a) $ map getHiding ts
    Just x  -> find [] (rangedThing x) (getHiding a) ts
  where
    upto h [] = Nothing
    upto h (NotHidden : _) = Nothing
    upto h (h' : _) | sameHiding h h' = Just []
    upto h (h' : hs) = (h' :) <$> upto h hs

    find :: [Hiding] -> ArgName -> Hiding -> [Arg ArgName] -> ImplicitInsertion
    find _ x _ (a@(Arg{}) : _) | visible a = NoSuchName x
    find hs x hidingx (a@(Arg _ y) : ts)
      | x == y && sameHiding hidingx a = impInsert $ reverse hs
      | x == y && sameHiding hidingx a = BadImplicits
      | otherwise = find (getHiding a : hs) x hidingx ts
    find i x _ [] = NoSuchName x
