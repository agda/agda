{- | Contains the syntax of the size types and signatures.
-}
module Agda.Termination.TypeBased.Syntax
 ( Size ( SUndefined, SDefined )
 , SizeType ( SizeTree, SizeGenericVar, SizeArrow, SizeGeneric )
 , SizeBound ( SizeUnbounded, SizeBounded )
 , SizeSignature ( SizeSignature, sigTele, sigBounds)
 , FreeGeneric (..)
 , pattern UndefinedSizeType
 , sizeCodomain
 , sizeSigArity
 ) where

import Control.DeepSeq ( NFData ( rnf ) )
import Agda.Syntax.Position ( KillRange ( killRange ) )
import qualified Data.List as List
import Data.Char ( chr, ord )
import Agda.Syntax.Common.Pretty ( Pretty ( pretty, prettyPrec, prettyList ), Doc, (<+>), text, prettyList_, (<>), parens )
import Agda.TypeChecking.Polarity.Base ( Polarity)

-- | An atomic size expression.
data Size
  = SUndefined
  -- ^ Undefined size, roughly corresponds to an infinite ordinal.
  | SDefined Int
  -- ^ Size variable.
  deriving (Eq, Show)

-- | A representation of a sized type, which is assigned to elements of underlying theory.
-- In our case, the theory is (something like) System Fω, so we reflect the arrow types and type abstractions.
data SizeType
  = SizeTree Size Size [(Polarity, SizeType)]
  -- ^ Endpoint size type that corresponds to a datatype.
  --   Every datatype has an assigned an inductive and coinductive size variables, which intuitively represent its depth, and a sequence of polarized parameters.
  --   For example, the datatype @List A@ has one parameter apart its size, so it can be encoded as '(⁺t₀,⁻∞)<+ε₀>', where ⁺ and ⁻ indicate that
  --  the variables are inductive and coinductive correspondingly. Since List is a purely inductive datatype, its coinductive size is undefined.
  | SizeArrow SizeType SizeType
  -- ^ Reflects the first-order abstraction in System Fω.
  | SizeGeneric Int SizeType
  -- ^ Reflects the second-order abstraction in System Fω. Throughout the implementation, we use the word 'Generic' to refer to the second-order parameterized variables.
  --
  --   The first argument indicates the _arity_ of the abstracted symbol.
  --   The reason for introducing arity is the popularity of Σ-types in Agda. Recall that Σ-type has type signature (A : Set) -> (B : A -> Set) -> Set.
  --   It is often the case that `B` is instantiated to a constant family, or some other parameterized inductive type in which shape we are interested (like B := List).
  --   It means that we need to track the number of applied arguments to the usages of B in order to correctly guess the shape of the type when it is finally used.
  --
  --   Generic variables are stored in the form of De Bruijn encoding.
  --
  --   These constructors are printed as 'Λ₁E', where the 'Λ' can be thought of as a type-level lambda which introduces a binding for the remaining expression,
  --   and '₁' is the arity of the generic
  | SizeGenericVar Int Int
  -- ^ A usage of generic variable.
  --   The first argument is a number of currently applied arguments to a generic variable
  --   The second argument id of the generic variable, which should be bound by the enclosing 'SizeGeneric' in complete signatures.
  --
  --   Generic variables are printed as '₁ε₂', where '₁' represents the number of _currently applied arguments_, and '₂' is an index of the binding.
  --   As with the constructor 'SizeGeneric', 'ε' does not carry special meaning and it is just a representation of a generic variable.
  deriving (Eq, Show)

-- Represents a free variable obtained during the processing of a De Bruijn-indexed term.
data FreeGeneric = FreeGeneric { fgArity :: Int, fgIndex :: Int }


-- | Represents an undefined size type.
-- Often used as a shortcut to processing.
-- The motivation is that since there is a loss of information, then it makes no sense to proceed with the size checking.
pattern UndefinedSizeType :: SizeType
pattern UndefinedSizeType = SizeTree SUndefined SUndefined []

-- | Decomposes size type to number of domains and a codomain.
sizeCodomain :: SizeType -> (Int, SizeType)
sizeCodomain s@(SizeTree _ _ _) = (0, s)
sizeCodomain s@(SizeGenericVar _ _) = (0, s)
sizeCodomain (SizeArrow l r) = (\(a, b) -> (a + 1, b)) (sizeCodomain r)
sizeCodomain (SizeGeneric _ r) = (\(a, b) -> (a + 1, b)) (sizeCodomain r)

-- | Represents a bound of a size variable.
data SizeBound = SizeUnbounded | SizeBounded Int
  deriving (Eq, Show)

-- | The top-level description of a size type of a definition.
data SizeSignature = SizeSignature
  { sigBounds :: [SizeBound]
  -- ^ The list of bounds for the size variables of the definition.
  --   All references point within the same list: if @SizeBounded i@ is an element of `sigBounds`, then `i < length sigBounds`.
  , sigTele :: SizeType
  -- ^ The size type of the definition.
  }
  deriving Show

sizeSigArity :: SizeSignature -> Int
sizeSigArity (SizeSignature bounds _) = length bounds

instance NFData Size where
  rnf :: Size -> ()
  rnf SUndefined = ()
  rnf (SDefined s) = s `seq` ()

instance Pretty Size where
  pretty :: Size -> Doc
  pretty SUndefined = "∞"
  pretty (SDefined x) = "t" <> (small x)

instance Pretty FreeGeneric where
  pretty (FreeGeneric a i) = "〈" <> small a <> "ε" <> small i <> "〉"

instance NFData SizeType where
  rnf (SizeTree sizeInd sizeCoind rest) = rnf sizeInd `seq` rnf sizeCoind `seq` rnf rest
  rnf (SizeGenericVar params i) = rnf params `seq` rnf i
  rnf (SizeArrow l r) = rnf l `seq` rnf r
  rnf (SizeGeneric args rest) = rnf args `seq` rnf rest

instance Pretty SizeType where
  pretty (SizeTree sizeInd sizeCoind tree) =
    let sizes
          | sizeCoind == SUndefined = "⁺" <> pretty sizeInd
          | sizeInd == SUndefined = "⁻" <> pretty sizeCoind
          | otherwise = "(⁺" <> pretty sizeInd <> ",⁻" <> pretty sizeCoind <> ")"
    in sizes <> (if null tree then "" else "<" <> prettyList_ (map (\(p, t) -> pretty p <> pretty t) tree) <> ">")
  pretty (SizeGeneric args rest) =
    let argrep = if args == 0 then "" else small args
    in ("∀" <> argrep <> "E" <> ".") <+> pretty rest
  pretty (SizeGenericVar args i) = (if args == 0 then "" else small args) <> "ε" <> (small i)
  pretty (SizeArrow s t) = (case s of
    SizeTree _ _ _ -> pretty s
    SizeGenericVar _ _ -> pretty s
    _ -> parens (pretty s))
    <+> "→" <+> pretty t


instance NFData SizeBound where
  rnf SizeUnbounded = ()
  rnf (SizeBounded i) = rnf i

instance Pretty SizeBound where
  pretty SizeUnbounded = "∞"
  pretty (SizeBounded i) = "<" <> pretty i


instance NFData SizeSignature where
  rnf :: SizeSignature -> ()
  rnf (SizeSignature args tele) = rnf args `seq` rnf tele

instance Pretty SizeSignature where
  pretty :: SizeSignature -> Doc
  pretty (SizeSignature abstracts tele) = "∀[" <> prettyList_ abstracts <> "]. " <> pretty tele

instance KillRange SizeSignature where
  killRange = id

-- Prints a number as a subscript.
small :: Int -> Doc
small i = text $ map (\c -> chr (ord c + 0x2080 - ord '0')) (show i)
