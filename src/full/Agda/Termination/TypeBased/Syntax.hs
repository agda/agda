{- | Contains the syntax of the size types and signatures.
-}
module Agda.Termination.TypeBased.Syntax
 ( Size ( SUndefined, SDefined )
 , SizeTele ( SizeTree, SizeGenericVar, SizeArrow, SizeGeneric )
 , SizeBound ( SizeUnbounded, SizeBounded )
 , SizeSignature ( SizeSignature )
 , pattern StoredGeneric
 , pattern UndefinedSizeTele
 , sizeCodomain
 , sizeSigArity
 ) where

import Control.DeepSeq ( NFData ( rnf ) )
import Agda.Syntax.Position ( KillRange ( killRange ) )
import qualified Data.List as List
import Data.Char ( chr, ord )

-- | An atomic size expression.
data Size
  = SUndefined
  -- ^ Undefined size, roughly corresponds to an infinite ordinal
  | SDefined Int
  -- ^ Size variable
  deriving Eq

-- | A representation of sized type, which is assigned to elements of underlying theory.
-- In our case, the theory is (something like) System Fω, so we reflect the arrow types and type abstractions.
data SizeTele
  = SizeTree Size [SizeTele]
  -- ^ Endpoint size type that corresponds to a datatype.
  --   Every datatype has an assigned size variable, which intuitively represents its depth, and a sequence of parameters.
  --   For example, the datatype @List A@ has one parameter apart its size, so it can be encoded as t₀<ε₀>.
  | SizeArrow SizeTele SizeTele
  -- ^ Reflects the first-order abstraction in System Fω.
  | SizeGeneric Int Int SizeTele
  -- ^ Reflects the second-order abstraction in System Fω. Throughout the implementation, we use the word 'Generic' to refer to the second-order parameterized variables.
  --
  --   The first argument indicates the _arity_ of the abstracted symbol.
  --   The reason for introducing arity is the popularity of Σ-types in Agda. Recall that Σ-type has type signature (A : Set) -> (B : A -> Set) -> Set.
  --   It is often the case that `B` is instantiated to a constant family, or some other parameterized inductive type in which shape we are interested (like B := List).
  --   It means that we need to track the number of applied arguments to the usages of B in order to correctly guess the shape of the type when it is finally used.
  --
  --   The second argument is the identifier of generic variable. This identifier can occurr in the third argument, which is the body of the second-order abstraction.
  --
  --   These constructors are printed as 'Λ₁ε₂', where the 'Λ' can be thought of as a type-level lambda which introduces a binding for the remaining expression,
  --   '₁' is the arity of the generic, and '₂' is the index of introduced binding. 'ε' is just a representation of a generic with no particular meaning behind this choice.
  | SizeGenericVar Int Int
  -- ^ A usage of generic variable.
  --   The first argument is a number of currently applied arguments to a generic variable
  --   The second argument id of the generic variable, which should be bound by the enclosing SizeGeneric in complete signatures.
  --
  --   Generic variables are printed as '₁ε₂', where '₁' represents the number of _currently applied arguments_, and '₂' is an index of the binding.
  --   As with the constructor 'SizeGeneric', 'ε' does not carry special meaning and it is just a representation of a generic variable.
  deriving Eq

-- | Represents a dangling generic variable.
-- This is used internally during the process of type-based termination.
pattern StoredGeneric :: Int -> Int -> SizeTele
pattern StoredGeneric args i  = SizeGeneric args i (SizeGenericVar (-1) (-1))

-- | Represents an undefined size type.
-- Often used as a shortcut to processing.
-- The motivation is that since there is a loss of information, then it makes no sense to proceed with the size checking.
pattern UndefinedSizeTele :: SizeTele
pattern UndefinedSizeTele = SizeTree SUndefined []

-- | Decomposes size type to number of domains and a codomain.
sizeCodomain :: SizeTele -> (Int, SizeTele)
sizeCodomain s@(SizeTree _ _) = (0, s)
sizeCodomain s@(SizeGenericVar _ _) = (0, s)
sizeCodomain s@(StoredGeneric args i) = (0, s)
sizeCodomain (SizeArrow l r) = (\(a, b) -> (a + 1, b)) (sizeCodomain r)
sizeCodomain (SizeGeneric _ _ r) = (\(a, b) -> (a + 1, b)) (sizeCodomain r)

-- | Represents a bound of a size variable.
data SizeBound = SizeUnbounded | SizeBounded Int
  deriving Eq

-- | The top-level description of a size type of a definition.
data SizeSignature = SizeSignature
  { sigBounds :: [SizeBound]
  -- ^ The list of bounds for the size variables of the definition.
  --   All references point within the same list: if @SizeBounded i@ is an element of `sigBounds`, then `i < length sigBounds`.
  , sigContra :: [Int]
  -- ^ The list of contravariant variables in the definition.
  --   A variable is contravariant if it was obtained from encoding a coinductive type.
  , sigTele :: SizeTele
  -- ^ The size type of the definition.
  }


sizeSigArity :: SizeSignature -> Int
sizeSigArity (SizeSignature bounds _ _) = length bounds

instance NFData SizeTele where
  rnf (SizeTree size rest) = rnf size `seq` rnf rest
  rnf (SizeGenericVar params i) = rnf params `seq` rnf i
  rnf (SizeArrow l r) = rnf l `seq` rnf r
  rnf (SizeGeneric args i rest) = rnf args `seq` rnf i `seq` rnf rest

instance Show SizeTele where
  show (SizeTree size tree) = show size ++ (if null tree then "" else "<" ++ concat (List.intersperse ", " (map show tree)) ++ ">")
  show (StoredGeneric args i) =
    let argrep = if args == 0 then "" else small args
    in "〈" ++ argrep ++ "ε" ++ small i ++ "〉"
  show (SizeGeneric args i rest) =
    let argrep = if args == 0 then "" else small args
    in "Λ" ++ argrep ++ "ε" ++ (small i) ++ ". " ++ show rest
  show (SizeGenericVar args i) = (if args == 0 then "" else small args) ++ "ε" ++ (small i)
  show (SizeArrow s t) = (case s of
    SizeTree _ _ -> show s ++ " -> "
    SizeGenericVar _ _ -> show s ++ " -> "
    _ -> "(" ++ show s ++ ") -> ")
    ++ show t


instance NFData SizeBound where
  rnf SizeUnbounded = ()
  rnf (SizeBounded i) = rnf i

instance Show SizeBound where
  show SizeUnbounded = "∞"
  show (SizeBounded i) = "<" ++ show i


instance NFData SizeSignature where
  rnf :: SizeSignature -> ()
  rnf (SizeSignature args contra tele) = rnf args `seq` rnf contra `seq` rnf tele

instance Show SizeSignature where
  show :: SizeSignature -> String
  show (SizeSignature abstracts contra tele) = "(" ++ concat (List.intersperse ", " (map show contra)) ++ ")∀[" ++ concat (List.intersperse ", " (map show abstracts)) ++ "]. " ++ show tele

instance KillRange SizeSignature where
  killRange = id


instance NFData Size where
  rnf :: Size -> ()
  rnf SUndefined = ()
  rnf (SDefined s) = s `seq` ()

instance Show Size where
  show :: Size -> String
  show SUndefined = "∞"
  show (SDefined x) = "t" ++ (small x)

small :: Int -> String
small i = map (\c -> chr (ord c + 0x2080 - ord '0')) (show i)
