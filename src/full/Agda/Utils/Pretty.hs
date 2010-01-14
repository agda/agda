{-| Pretty printing functions.
-}
module Agda.Utils.Pretty
    ( module Agda.Utils.Pretty
    , module Text.PrettyPrint
    ) where

import Text.PrettyPrint

class Pretty a where
    pretty	:: a -> Doc
    prettyPrec	:: Int -> a -> Doc

    pretty	= prettyPrec 0
    prettyPrec	= const pretty

instance Pretty Doc where
    pretty = id

pwords :: String -> [Doc]
pwords = map text . words

fwords :: String -> Doc
fwords = fsep . pwords

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
