{-# OPTIONS_GHC -Wunused-imports #-}

-- | Ensures that all occurences of an abstract name share
-- the same concrete name.
--
-- Apply this transformation if your backend uses concrete names
-- for identification purposes!
--
-- The identity of an abstract name is only the nameId, the concrete
-- name is only a naming suggestion. If renaming imports are used,
-- the concrete name may change. This transformation makes sure
-- that all occurences of an abstract name share the same
-- concrete name.
--
-- This transfomation should be run as the last transformation.
module Agda.Compiler.Treeless.NormalizeNames ( normalizeNames ) where

import Agda.TypeChecking.Monad
import Agda.Syntax.Treeless

normalizeNames :: TTerm -> TCM TTerm
normalizeNames = tr
  where
    tr = \case
      TDef q              -> TDef . defName <$> getConstInfo q
      t@TVar{}            -> return t
      t@TCon{}            -> return t
      t@TPrim{}           -> return t
      t@TLit{}            -> return t
      t@TUnit{}           -> return t
      t@TSort{}           -> return t
      t@TErased{}         -> return t
      t@TError{}          -> return t
      TLam b              -> TLam <$> tr b
      TApp a bs           -> TApp <$> tr a <*> mapM tr bs
      TLet e b            -> TLet <$> tr e <*> tr b
      TCase sc t def alts -> TCase sc t <$> tr def <*> mapM trAlt alts
      TCoerce a           -> TCoerce <$> tr a

    trAlt = \case
      TAGuard g b -> TAGuard <$> tr g <*> tr b
      TACon q a b -> TACon q a <$> tr b
      TALit l b   -> TALit l <$> tr b
