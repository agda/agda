{-# LANGUAGE CPP #-}

{-| Pretty printing functions.
-}
module Agda.Utils.Pretty
    ( module Agda.Utils.Pretty
    , module Text.PrettyPrint
    ) where

import Data.Int ( Int32 )

import Text.PrettyPrint hiding (TextDetails(Str), empty)

-- * Pretty class

-- | While 'Show' is for rendering data in Haskell syntax,
--   'Pretty' is for displaying data to the world, i.e., the
--   user and the environment.
--
--   Atomic data has no inner document structure, so just
--   implement 'pretty' as @pretty a = text $ ... a ...@.

class Pretty a where
  pretty      :: a -> Doc
  prettyPrec  :: Int -> a -> Doc

  pretty      = prettyPrec 0
  prettyPrec  = const pretty

-- | Use instead of 'show' when printing to world.

prettyShow :: Pretty a => a -> String
prettyShow = render . pretty

-- | Space separated list of pretty things.

prettyList :: Pretty a => [a] -> Doc
prettyList = sep . map (prettyPrec 10000)

-- * Pretty instances

instance Pretty Bool    where pretty = text . show
instance Pretty Int     where pretty = text . show
instance Pretty Int32   where pretty = text . show
instance Pretty Integer where pretty = text . show

instance Pretty Char where
  pretty c = text [c]

instance Pretty Doc where
  pretty = id

instance Pretty String where
  pretty = text

instance Pretty a => Pretty (Maybe a) where
  prettyPrec p Nothing  = text "Nothing"
  prettyPrec p (Just x) = mparens (p > 0) $ text "Just" <+> prettyPrec 10 x

-- * 'Doc' utilities

pwords :: String -> [Doc]
pwords = map text . words

fwords :: String -> Doc
fwords = fsep . pwords

-- ASR (2016-12-13): In pretty >= 1.1.2.0 the below function 'mparens'
-- is called 'maybeParens'. I didn't use that name due to the issue
-- https://github.com/haskell/pretty/issues/40.

-- | Apply 'parens' to 'Doc' if boolean is true.
mparens :: Bool -> Doc -> Doc
mparens True  = parens
mparens False = id

-- | @align max rows@ lays out the elements of @rows@ in two columns,
-- with the second components aligned. The alignment column of the
-- second components is at most @max@ characters to the right of the
-- left-most column.
--
-- Precondition: @max > 0@.

align :: Int -> [(String, Doc)] -> Doc
align max rows =
  vcat $ map (\(s, d) -> text s $$ nest (maxLen + 1) d) $ rows
  where maxLen = maximum $ 0 : filter (< max) (map (length . fst) rows)

-- | Handles strings with newlines properly (preserving indentation)
multiLineText :: String -> Doc
multiLineText = vcat . map text . lines

