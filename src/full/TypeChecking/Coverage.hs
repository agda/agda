{-# OPTIONS -cpp #-}

module TypeChecking.Coverage where

import Control.Monad

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Pattern
import TypeChecking.Monad.Base
import TypeChecking.Monad.Options
import TypeChecking.Pretty
import Utils.Permutation

#include "../undefined.h"

data SplitClause = SClause
      { scTel   :: Telescope      -- ^ type of variables in scPats
      , scPats  :: [Arg Pattern]
      , scSubst :: [Term]         -- ^ substitution from scTel to old context
      }

type Covering = [SplitClause]

typeOfVar :: Telescope -> Nat -> Type
typeOfVar tel n
  | n >= length ts  = __IMPOSSIBLE__
  | otherwise       = snd . unArg $ ts !! n
  where
    ts = reverse $ telToList tel

-- | split Δ x ps. Δ ⊢ ps, x ∈ Δ (deBruijn index)
split :: Telescope -> Permutation -> Nat -> [Arg Pattern] -> TCM Covering
split tel perm x ps = do
  reportSDoc "tc.cover.top" 10 $ vcat
    [ text "split"
    , nest 2 $ vcat
      [ text "tel  =" <+> prettyTCM tel
      , text "perm =" <+> text (show perm)
      , text "x    =" <+> text (show x)
      , text "ps   =" <+> text (show ps)
      ]
    ]

  let t     = typeOfVar tel x
      holes = reverse $ permute perm $ allHolesWithContents ps

  unless (length holes == length (telToList tel)) $
    fail "split: bad holes or tel"

  let (p, hps) = holes !! x

  reportSDoc "tc.cover.top" 10 $ nest 2 $ vcat $
    [ text "p   =" <+> text (show p)
    , text "hps =" <+> text (show hps)
    ]

  return []

