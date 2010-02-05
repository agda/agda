module Utils where

-- Standard Library Imports
import           Control.Applicative
import           Control.Arrow
import qualified Data.ByteString.Char8
  as BS
import           Text.Regex.Posix

--------------------------------------------------------------------------------

type MatchPair      = (MatchOffset, MatchLength)
type MatchTriple    = (BS.ByteString, (BS.ByteString, BS.ByteString))
type Substitution m = BS.ByteString -> m BS.ByteString

-- Yuck!
substitute :: (Functor m, Monad m)
           => BS.ByteString
           -> BS.ByteString
           -> Substitution m
           -> m BS.ByteString
substitute input regEx subst = output
                             $ splits 0 (getAllMatches (input =~ regEx)) input
  where
    splits :: Int -> [MatchPair] -> BS.ByteString -> [MatchTriple]
    splits _o []            _str = []
    splits  o ((mo, ml):ms)  str = splitter str
                                 : splits o' ms (BS.drop (o' - o) str)
      where
        o'       = mo + ml
        splitter = (***) id (BS.splitAt ml) . BS.splitAt (mo - o)
    output mts = BS.concat <$> mapM joiner mts
      where
        joiner mt = do
          v <- subst $ fst $ snd mt
          return $ BS.concat [fst mt, v]
