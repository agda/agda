{-|

  A position is a triple (filename, line, column).

-}

module Position(
  -- * Datatype
  Position(Position),
  -- * Special constructors
  noPosition, filePosition,
  -- * Modifiers
  remPositionFile, addColPos,
  -- * Printing
  prPosition,
  -- * access file name
  positionFile
) where

data Position =
    Position String Int Int     -- ^ file, line, pos
    deriving (Eq, Ord,Show)

-- | Print position information.
prPosition :: Position -> String
prPosition (Position f l c) =
    let lc = if l<0 then "" else "line "++show l ++ (if c < 0 then "" else ", column "++show c)
    in  case f of
            "" -> if null lc then "" else lc
            _ -> "\""++f ++ "\"" ++ (if null lc then "Unknown position" else ", "++lc)

-- | Empty position information.
noPosition :: Position
noPosition = Position "" (-1) (-1)

-- | Position containing only the filename.
filePosition :: String -> Position
filePosition f = Position f (-1) (-1)

-- | Remove filename component from position triple.
remPositionFile :: Position -> Position
remPositionFile (Position _ l c) = Position "" l c

-- | Increase column component by a given integer.
addColPos :: Position -> Int -> Position
addColPos (Position f l c) i = Position f l (c+i)


positionFile :: Position -> String
positionFile (Position f _ _ ) = f
