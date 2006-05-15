
module Utils.IO where

import qualified Prelude
import Utils.Unicode

print :: Prelude.Show a => a -> Prelude.IO ()
print x = putStrLn (Prelude.show x)

putStr :: Prelude.String -> Prelude.IO ()
putStr s = Prelude.putStr (toUTF8 s)

putStrLn :: Prelude.String -> Prelude.IO ()
putStrLn s = Prelude.putStrLn (toUTF8 s)

