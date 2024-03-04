
import System.Exit (die)
import Control.Monad (unless)
import Data.Char (isAscii)
import Data.List (findIndices)

main = do
  f <- lines <$> readFile "src/full/Agda/Syntax/Parser/Parser.y"

  let badLines = (+1) <$> findIndices (not . all isAscii) f

  unless (badLines == []) $ die $
    "Parser.y contains non-ASCII characters on lines "
    <> show badLines
