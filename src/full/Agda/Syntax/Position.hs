{-# OPTIONS -fglasgow-exts #-}

{-| Position information for syntax. Crucial for giving good error messages.
-}

module Agda.Syntax.Position
  ( -- * Positions
    Position(..)
  , startPos
  , noPos
  , movePos
  , movePosByString
  , backupPos

    -- * Ranges
  , Range(..)
  , HasRange(..)
  , SetRange(..)
  , noRange
  , fuseRange
  ) where

import Data.Generics
import Data.List

{--------------------------------------------------------------------------
    Types and classes
 --------------------------------------------------------------------------}

-- | Represents a point in the input (file, position, line, col) or
--   an unknown position
data Position = Pn { srcFile :: FilePath
                   , posPos  :: !Int
		   , posLine :: !Int
		   , posCol  :: !Int
		   }
	    | NoPos
    deriving (Typeable, Data, Eq, Ord)


-- | A range is a pair of positions. The @rEnd@ position is
--   not included in the range.
data Range = Range { rStart, rEnd :: !Position }
    deriving (Typeable, Data, Eq, Ord)


-- | Things that have a range are instances of this class.
class HasRange t where
    getRange :: t -> Range

instance HasRange Range where
    getRange = id

instance HasRange a => HasRange [a] where
    getRange = foldr fuseRange noRange

instance (HasRange a, HasRange b) => HasRange (a,b) where
    getRange = uncurry fuseRange

instance (HasRange a, HasRange b, HasRange c) => HasRange (a,b,c) where
    getRange (x,y,z) = getRange (x,(y,z))

-- | If it's also possible to set the range, this is the class.
--   It should hold that getRange (setRange r x) == r
class HasRange t => SetRange t where
  setRange :: Range -> t -> t

instance SetRange Range where
  setRange = const

{--------------------------------------------------------------------------
    Pretty printing
 --------------------------------------------------------------------------}

instance Show Position where
    show (Pn "" _ l c)	= show l ++ "," ++ show c
    show (Pn f  _ l c)	= f ++ ":" ++ show l ++ "," ++ show c
    show NoPos		= "<No position>"


instance Show Range where
    show (Range NoPos NoPos) = ""
    show (Range s e) = file ++ start ++ "-" ++ end
	where
	    f	= srcFile s
	    sl	= posLine s
	    el	= posLine e
	    sc	= posCol s
	    ec	= posCol e
	    file
		| null f    = ""
		| otherwise = f ++ ":"
	    start = show sl ++ "," ++ show sc
	    end
		| sl == el  = show ec
		| otherwise = show el ++ "," ++ show ec

{--------------------------------------------------------------------------
    Functions on postitions and ranges
 --------------------------------------------------------------------------}

-- | The first position in a file: position 1, line 1, column 1.
startPos :: FilePath -> Position
startPos f = Pn { srcFile = f, posPos = 1, posLine = 1, posCol = 1 }


-- | The unknown position.
noPos :: Position
noPos = NoPos


-- | Ranges between two unknown positions
noRange :: Range
noRange = Range NoPos NoPos


-- | Advance the position by one character.
--   A tab character (@'\t'@) will move the position to the next
--   tabstop (tab size is 8). A newline character (@'\n'@) moves
--   the position to the first character in the next line. Any
--   other character moves the position to the next column.
movePos :: Position -> Char -> Position
movePos (Pn f p l c) '\t' = Pn f (p + 1) l (div (c + 7) 8 * 8 + 1)
movePos (Pn f p l c) '\n' = Pn f (p + 1) (l + 1) 1
movePos (Pn f p l c) _	  = Pn f (p + 1) l (c + 1)
movePos NoPos _		  = NoPos


-- | Advance the position by a string.
--
--   > movePosByString = foldl' movePos
movePosByString :: Position -> String -> Position
movePosByString = foldl' movePos


-- | Backup the position by one character.
--
-- Precondition: The character must not be @'\t'@ or @'\n'@.
backupPos :: Position -> Position
backupPos (Pn f p l c) = Pn f (p - 1) l (c - 1)
backupPos NoPos        = NoPos


-- | Finds the least interval that covers its arguments.
fuseRange :: (HasRange t, HasRange u) => t -> u -> Range
fuseRange x y = Range start end
    where
	[rx,ry] = sort [getRange x, getRange y]
	start = case rStart rx of
		    NoPos   -> rStart ry
		    p	    -> p
	end   = case rEnd ry of
		    NoPos   -> rEnd rx
		    p	    -> p

