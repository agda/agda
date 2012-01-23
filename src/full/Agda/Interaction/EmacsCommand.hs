------------------------------------------------------------------------
-- | Low-level code for instructing Emacs to do things
------------------------------------------------------------------------

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Agda.Interaction.EmacsCommand
  ( Lisp(..)
  , response
  , putResponse
  ) where

import qualified Agda.Utils.IO.Locale as LocIO
import Agda.Utils.Pretty

-- | Simple Emacs Lisp expressions.

data Lisp a
  = A a
    -- ^ Atom.
  | Cons (Lisp a) (Lisp a)
    -- Cons cell.
  | L [Lisp a]
    -- ^ List.
  | Q (Lisp a)
    -- Quoted expression.

instance Pretty a => Pretty (Lisp a) where
  pretty (A a )     = pretty a
  pretty (Cons a b) = parens (pretty a <+> text "." <+> pretty b)
  pretty (L xs)     = parens (hsep (map pretty xs))
  pretty (Q x)      = text "'" <> pretty x

instance Pretty String where pretty = text

instance Pretty a => Show (Lisp a) where show = show . pretty

-- | Formats a response command.

response :: Lisp String -> String
response l = show (text "agda2_mode_code" <+> pretty l)

-- | Writes a response command to standard output.

putResponse :: Lisp String -> IO ()
putResponse = LocIO.putStrLn . response
