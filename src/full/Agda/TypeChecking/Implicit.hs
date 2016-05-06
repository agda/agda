{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}

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
--   and @expand@ holds on the hiding info of its domain. If @eti@ is
--   @ExplicitToInstance@, then explicit arguments are considered as instance
--   arguments.
implicitArgs :: Int -> (Hiding -> Bool) -> Type -> TCM (Args, Type)
implicitArgs n expand t = mapFst (map (fmap namedThing)) <$> do
  implicitNamedArgs n (\ h x -> expand h) t

-- | @implicitNamedArgs n expand eti t@ generates up to @n@ named implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding and name info of its domain. If @eti@ is
--   @ExplicitToInstance@, then explicit arguments are considered as instance
--   arguments.
implicitNamedArgs :: Int -> (Hiding -> ArgName -> Bool) -> Type -> TCM (NamedArgs, Type)
implicitNamedArgs 0 expand t0 = return ([], t0)
implicitNamedArgs n expand t0 = do
    t0' <- reduce t0
    case ignoreSharing $ unEl t0' of
      Pi (Dom info a) b | let x = absName b, expand (getHiding info) x -> do
          when (getHiding info /= Hidden) $
            reportSDoc "tc.term.args.ifs" 15 $
            text "inserting instance meta for type" <+> prettyTCM a
          v  <- applyRelevanceToContext (getRelevance info) $
                newMeta (getHiding info) (argNameToString x) a
          let narg = Arg info (Named (Just $ unranged x) v)
          mapFst (narg :) <$> implicitNamedArgs (n-1) expand (absApp b v)
      _ -> return ([], t0')
  where
    newMeta :: Hiding -> String -> Type -> TCM Term
    newMeta Hidden   = newNamedValueMeta RunMetaOccursCheck
    newMeta Instance = newIFSMeta
    newMeta NotHidden = newIFSMeta

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
insertImplicit a ts | notHidden a = impInsert $ nofHidden ts
  where
    nofHidden :: [Arg a] -> [Hiding]
    nofHidden = takeWhile (NotHidden /=) . map getHiding
insertImplicit a ts =
  case nameOf (unArg a) of
    Nothing -> maybe BadImplicits impInsert $ upto (getHiding a) $ map getHiding ts
    Just x  -> find [] (rangedThing x) (getHiding a) ts
  where
    upto h [] = Nothing
    upto h (NotHidden:_) = Nothing
    upto h (h':_) | h == h' = Just []
    upto h (h':hs) = (h':) <$> upto h hs
    find :: [Hiding] -> ArgName -> Hiding -> [Arg ArgName] -> ImplicitInsertion
    find _ x _ (a@(Arg{}) : _) | notHidden a = NoSuchName x
    find hs x hidingx (a@(Arg _ y) : ts)
      | x == y && hidingx == getHiding a = impInsert $ reverse hs
      | x == y && hidingx /= getHiding a = BadImplicits
      | otherwise = find (getHiding a:hs) x hidingx ts
    find i x _ []                            = NoSuchName x
