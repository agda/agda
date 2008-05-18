
module PreludeString where
import RTP -- magic module

import PreludeList
open   PreludeList using (List)

open import AlonzoPrelude


infixr 50 _++_



private
    primitive
      primStringAppend	 : String -> String -> String
      -- primStringReverse  : String -> String
      primStringToList	 : String -> List Char
      primStringFromList : List Char -> String
      
_++_     = primStringAppend
reverseString = RTP.primStringReverse

toList : String -> List Char
toList = primStringToList


fromList : List Char -> String
fromList = primStringFromList

-- toList   = RTP.primStringToList
-- fromList = RTP.primStringFromList

