{-# OPTIONS -fglasgow-exts #-}

{-| Position information for syntax. Crucial for giving good error messages.
-}

module Syntax.Position
  ( -- * Positions
    Position(..)
  , startPos
  , noPos
  , movePos
  , movePosByString

    -- * Ranges
  , Range(..)
  , HasRange(..)
  , noRange
  , fuseRange
  ) where

import Data.Generics
import Data.List

{--------------------------------------------------------------------------
    Types and classes
 --------------------------------------------------------------------------}

-- | Represents a point in the input (file, line, col) or
--   an unknown position
data Position = Pn { srcFile :: FilePath
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

{--------------------------------------------------------------------------
    Pretty printing
 --------------------------------------------------------------------------}

instance Show Position where
    show (Pn "" l c)	= show l ++ "," ++ show c
    show (Pn f l c)	= f ++ ":" ++ show l ++ "," ++ show c
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

-- | The first position in a file: line 1, column 1.
startPos :: FilePath -> Position
startPos f = Pn { srcFile = f, posLine = 1, posCol = 1 }


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
movePos (Pn f l c) '\t'	= Pn f l (div (c + 7) 8 * 8 + 1)
movePos (Pn f l c) '\n'	= Pn f (l + 1) 1
movePos (Pn f l c) _	= Pn f l (c + 1)
movePos NoPos _		= NoPos


-- | Advance the position by a string.
--
--   > movePosByString = foldl' movePos
movePosByString :: Position -> String -> Position
movePosByString = foldl' movePos


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

