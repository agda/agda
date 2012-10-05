{-# LANGUAGE CPP #-}

{-| Functions for inserting implicit arguments at the right places.
-}
module Agda.TypeChecking.Implicit where

import Control.Applicative
import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import {-# SOURCE #-} Agda.TypeChecking.InstanceArguments

import Agda.Utils.Size
import Agda.Utils.Tuple

#include "../undefined.h"
import Agda.Utils.Impossible


-- | @implicitArgs n expand t@ generates up to @n@ implicit arguments
--   metas (unbounded if @n<0@), as long as @t@ is a function type
--   and @expand@ holds on the hiding info of its domain.
implicitArgs :: Int -> (Hiding -> Bool) -> Type -> TCM (Args, Type)
implicitArgs 0 expand t0 = return ([], t0)
implicitArgs n expand t0 = do
    t0' <- reduce t0
    case ignoreSharing $ unEl t0' of
      Pi (Dom h rel a) b | expand h -> do
          when (h == Instance) $ reportSLn "tc.term.args.ifs" 15 $
            "inserting implicit meta for type " ++ show a
          v  <- applyRelevanceToContext rel $ newMeta h (absName b) a
          let arg = Arg h rel v
          mapFst (arg:) <$> implicitArgs (n-1) expand (absApp b v)
      _ -> return ([], t0')
  where
    newMeta Hidden   = newNamedValueMeta RunMetaOccursCheck
    newMeta Instance = initializeIFSMeta
    newMeta _        = __IMPOSSIBLE__

{- UNUSED, BUT DONT REMOVE (Andreas, 2012-07-31)
introImplicits :: (Hiding -> Bool) -> Type -> (Int -> Type -> TCM a) -> TCM a
introImplicits expand t cont = do
  TelV tel t0 <- telViewUpTo' (-1) (expand . domHiding) t
  addCtxTel tel $ cont (size tel) t0
-}

{- POINTLESS, NEEDS TO BE CONTINUATION-PASSING
-- | @introImplicits expand t@ introduces domain types of @t@
--   into the context, as long as @expand@ holds on them.
introImplicits :: (Hiding -> Bool) -> Type -> TCM (Int, Type)
introImplicits expand t = do
  t <- reduce t
  case unEl t of
    Pi dom@(Dom h rel a) b | expand h ->
      addCtxString (absName b) dom $ do
        mapFst (+1) <$> introImplicits expand (absBody b)
    _ -> return (0, t)
-}

---------------------------------------------------------------------------

data ImplicitInsertion
      = ImpInsert [Hiding]	  -- ^ this many implicits have to be inserted
      | BadImplicits	  -- ^ hidden argument where there should have been a non-hidden arg
      | NoSuchName String -- ^ bad named argument
      | NoInsertNeeded
  deriving (Show)

impInsert :: [Hiding] -> ImplicitInsertion
impInsert [] = NoInsertNeeded
impInsert hs = ImpInsert hs

-- | The list should be non-empty.
insertImplicit :: NamedArg e -> [Arg String] -> ImplicitInsertion
insertImplicit _ [] = __IMPOSSIBLE__
insertImplicit a ts | argHiding a == NotHidden = impInsert $ nofHidden ts
  where
    nofHidden :: [Arg a] -> [Hiding]
    nofHidden = takeWhile (NotHidden /=) . map argHiding
insertImplicit a ts =
  case nameOf (unArg a) of
    Nothing -> maybe BadImplicits impInsert $ upto (argHiding a) $ map argHiding ts
    Just x  -> find [] x (argHiding a) ts
  where
    upto h [] = Nothing
    upto h (NotHidden:_) = Nothing
    upto h (h':_) | h == h' = Just []
    upto h (h':hs) = (h':) <$> upto h hs
    find _ x _ (Arg NotHidden _ _ : _) = NoSuchName x
    find hs x hidingx (Arg hidingy r y : ts)
      | x == y && hidingx == hidingy = impInsert $ reverse hs
      | x == y && hidingx /= hidingy = BadImplicits
      | otherwise = find (hidingy:hs) x hidingx ts
    find i x _ []			     = NoSuchName x
