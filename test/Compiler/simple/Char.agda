open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

mapString : (Char → Char) → String → String
mapString f s = primStringFromList (map f (primStringToList s))

and : Bool → Bool → Bool
and true  true  = true
and _     _     = false

_∧_ : Bool → Bool → Bool
_∧_ = and

all : {A : Set} → (A → Bool) → List A → Bool
all p []       = true
all p (x ∷ xs) = p x ∧ all p xs

allString : (Char → Bool) → String → Bool
allString p s = all p (primStringToList s)

not : Bool → Bool
not false = true
not true  = false

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

fromCount : Nat → Nat → List Nat
fromCount 0 _ = []
fromCount (suc n) a = a ∷ fromCount n (suc a)

fromTo : Nat → Nat → List Nat
fromTo a b = fromCount (suc b - a) a

postulate
  putStrLn : String → IO ⊤
  _>>_ : {A B : Set} → IO A → IO B → IO B

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE GHC _>>_ = \ _ _ -> (>>) #-}
{-# COMPILE JS putStrLn = x => y => (console.log(x), y) #-}
{-# COMPILE JS _>>_ = _ => _ => x => y => z => y(x(z)) #-}

assert : String → Bool → IO ⊤
assert s true  = putStrLn (primStringAppend s " PASSED")
assert s false = putStrLn (primStringAppend s " FAILED")

listNatEquality : List Nat → List Nat → Bool
listNatEquality []       []       = true
listNatEquality (x ∷ xs) (y ∷ ys) = (x == y) ∧ listNatEquality xs ys
listNatEquality _        _        = false

listAppend : List Nat → List Nat → List Nat
listAppend []       ys = ys
listAppend (x ∷ xs) ys = x ∷ listAppend xs ys

_++_ : List Nat → List Nat → List Nat
_++_ = listAppend

main : IO ⊤
main = do
  let controlSpaceCodes = fromTo 0x0009 0x000D -- tab, line feed, vertical tab, form feed, carriage return
  let controlSpace = "\t\n\v\f\r"
  let spaceCodes = fromTo 0x2000 0x200A ++ (0x202F ∷ 0x205F ∷ 0x3000 ∷ [])
  let space = primStringFromList (map primNatToChar spaceCodes)
  let asciiDigitCodes = fromTo 0x0030 0x0039
  let asciiDigit = "0123456789"
  let latinSmallCodes = fromTo 0x0061 0x007A
  let latinSmall = "abcdefghijklmnopqrstuvwxyz"
  let latinSmallA-F = "abcdef"
  let latinSmallG-Z = "ghijklmnopqrstuvwxyz"
  let latinCapitalCodes = fromTo 0x0041 0x005A
  let latinCapital = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  let latinCapitalA-F = "ABCDEF"
  let latinCapitalG-Z = "GHIJKLMNOPQRSTUVWXYZ"
  let latinSmallSupplementCodes = fromTo 0x00E0 0x00F6 ++ fromTo 0x00F8 0x00FE -- à to þ, excluding ÷
  let latinSmallSupplement = primStringFromList (map primNatToChar latinSmallSupplementCodes)
  let latinCapitalSupplementCodes = fromTo 0x00C0 0x00D6 ++ fromTo 0x00D8 0x00DE -- À to Þ, excluding ×
  let latinCapitalSupplement = primStringFromList (map primNatToChar latinCapitalSupplementCodes)
  let circledLatinSmallLetterCodes = fromTo 0x24D0 0x24E9 -- ⓐ to ⓩ
  let circledLatinSmallLetter = primStringFromList (map primNatToChar circledLatinSmallLetterCodes)
  let circledLatinCapitalLetterCodes = fromTo 0x24B6 0x24CF -- Ⓐ to Ⓩ
  let circledLatinCapitalLetter = primStringFromList (map primNatToChar circledLatinCapitalLetterCodes)
  let cjkUnifiedCodes = fromTo 0x4E00 0x4EFF -- "一" to "仿", a few CJK Unified Ideographs
  let cjkUnified = primStringFromList (map primNatToChar cjkUnifiedCodes)

  -- control spaces
  assert "control spaces                   - not primIsLower    " (allString (not ∘ primIsLower) controlSpace)
  assert "control spaces                   - not primIsDigit    " (allString (not ∘ primIsDigit) controlSpace)
  assert "control spaces                   - not primIsAlpha    " (allString (not ∘ primIsAlpha) controlSpace)
  assert "control spaces                   - primIsSpace        " (allString primIsSpace controlSpace)
  assert "control spaces                   - primIsAscii        " (allString primIsAscii controlSpace)
  assert "control spaces                   - primIsLatin1       " (allString primIsLatin1 controlSpace)
  assert "control spaces                   - not primIsPrint    " (allString (not ∘ primIsPrint) controlSpace)
  assert "control spaces                   - not primIsHexDigit " (allString (not ∘ primIsHexDigit) controlSpace)
  assert "control spaces                   - primToUpper        " (primStringEquality controlSpace (mapString primToUpper controlSpace))
  assert "control spaces                   - primToLower        " (primStringEquality controlSpace (mapString primToLower controlSpace))
  assert "control spaces                   - primCharToNat      " (listNatEquality controlSpaceCodes (map primCharToNat (primStringToList controlSpace)))
  assert "control spaces                   - primNatToChar      " (primStringEquality controlSpace (primStringFromList (map primNatToChar controlSpaceCodes)))

  -- spaces
  assert "spaces                           - not primIsLower    " (allString (not ∘ primIsLower) space)
  assert "spaces                           - not primIsDigit    " (allString (not ∘ primIsDigit) space)
  assert "spaces                           - not primIsAlpha    " (allString (not ∘ primIsAlpha) space)
  assert "spaces                           - primIsSpace        " (allString primIsSpace space)
  assert "spaces                           - not primIsAscii    " (allString (not ∘ primIsAscii) space)
  assert "spaces                           - not primIsLatin1   " (allString (not ∘ primIsLatin1) space)
  assert "spaces                           - primIsPrint        " (allString primIsPrint space)
  assert "spaces                           - not primIsHexDigit " (allString (not ∘ primIsHexDigit) space)
  assert "spaces                           - primToUpper        " (primStringEquality space (mapString primToUpper space))
  assert "spaces                           - primToLower        " (primStringEquality space (mapString primToLower space))

  -- ascii digits
  assert "ascii digits                     - not primIsLower    " (allString (not ∘ primIsLower) asciiDigit)
  assert "ascii digits                     - primIsDigit        " (allString primIsDigit asciiDigit)
  assert "ascii digits                     - not primIsAlpha    " (allString (not ∘ primIsAlpha) asciiDigit)
  assert "ascii digits                     - not primIsSpace    " (allString (not ∘ primIsSpace) asciiDigit)
  assert "ascii digits                     - primIsAscii        " (allString primIsAscii asciiDigit)
  assert "ascii digits                     - primIsLatin1       " (allString primIsLatin1 asciiDigit)
  assert "ascii digits                     - primIsPrint        " (allString primIsPrint asciiDigit)
  assert "ascii digits                     - primIsHexDigit     " (allString primIsHexDigit asciiDigit)
  assert "ascii digits                     - primToUpper        " (primStringEquality asciiDigit (mapString primToUpper asciiDigit))
  assert "ascii digits                     - primToLower        " (primStringEquality asciiDigit (mapString primToLower asciiDigit))
  assert "ascii digits                     - primCharToNat      " (listNatEquality asciiDigitCodes (map primCharToNat (primStringToList asciiDigit)))
  assert "ascii digits                     - primNatToChar      " (primStringEquality asciiDigit (primStringFromList (map primNatToChar asciiDigitCodes)))

  -- latin small letters
  assert "latin small letters              - primIsLower        " (allString primIsLower latinSmall)
  assert "latin small letters              - not primIsDigit    " (allString (not ∘ primIsDigit) latinSmall)
  assert "latin small letters              - primIsAlpha        " (allString primIsAlpha latinSmall)
  assert "latin small letters              - not primIsSpace    " (allString (not ∘ primIsSpace) latinSmall)
  assert "latin small letters              - primIsAscii        " (allString primIsAscii latinSmall)
  assert "latin small letters              - primIsLatin1       " (allString primIsLatin1 latinSmall)
  assert "latin small letters              - primIsPrint        " (allString primIsPrint latinSmall)
  assert "latin small letters (A - F)      - primIsHexDigit     " (allString primIsHexDigit latinSmallA-F)
  assert "latin small letters (G - Z)      - not primIsHexDigit " (allString (not ∘ primIsHexDigit) latinSmallG-Z)
  assert "latin small letters              - primToUpper        " (primStringEquality latinCapital (mapString primToUpper latinSmall))
  assert "latin small letters              - primToLower        " (primStringEquality latinSmall (mapString primToLower latinSmall))
  assert "latin small letters              - primCharToNat      " (listNatEquality latinSmallCodes (map primCharToNat (primStringToList latinSmall)))
  assert "latin small letters              - primNatToChar      " (primStringEquality latinSmall (primStringFromList (map primNatToChar latinSmallCodes)))

  -- latin capital letters
  assert "latin capital letters            - not primIsLower    " (allString (not ∘ primIsLower) latinCapital)
  assert "latin capital letters            - not primIsDigit    " (allString (not ∘ primIsDigit) latinCapital)
  assert "latin capital letters            - primIsAlpha        " (allString primIsAlpha latinCapital)
  assert "latin capital letters            - not primIsSpace    " (allString (not ∘ primIsSpace) latinCapital)
  assert "latin capital letters            - primIsAscii        " (allString primIsAscii latinCapital)
  assert "latin capital letters            - primIsLatin1       " (allString primIsLatin1 latinCapital)
  assert "latin capital letters            - primIsPrint        " (allString primIsPrint latinCapital)
  assert "latin capital letters (A - F)    - primIsHexDigit     " (allString primIsHexDigit latinCapitalA-F)
  assert "latin capital letters (G - Z)    - not primIsHexDigit " (allString (not ∘ primIsHexDigit) latinCapitalG-Z)
  assert "latin capital letters            - primToUpper        " (primStringEquality latinCapital (mapString primToUpper latinCapital))
  assert "latin capital letters            - primToLower        " (primStringEquality latinSmall (mapString primToLower latinCapital))
  assert "latin capital letters            - primCharToNat      " (listNatEquality latinCapitalCodes (map primCharToNat (primStringToList latinCapital)))
  assert "latin capital letters            - primNatToChar      " (primStringEquality latinCapital (primStringFromList (map primNatToChar latinCapitalCodes)))

  -- latin small letters supplement
  assert "latin small latters supplement   - primIsLower        " (allString primIsLower latinSmallSupplement)
  assert "latin small latters supplement   - not primIsDigit    " (allString (not ∘ primIsDigit) latinSmallSupplement)
  assert "latin small latters supplement   - primIsAlpha        " (allString primIsAlpha latinSmallSupplement)
  assert "latin small latters supplement   - not primIsSpace    " (allString (not ∘ primIsSpace) latinSmallSupplement)
  assert "latin small latters supplement   - not primIsAscii    " (allString (not ∘ primIsAscii) latinSmallSupplement)
  assert "latin small latters supplement   - primIsLatin1       " (allString primIsLatin1 latinSmallSupplement)
  assert "latin small latters supplement   - primIsPrint        " (allString primIsPrint latinSmallSupplement)
  assert "latin small latters supplement   - not primIsHexDigit " (allString (not ∘ primIsHexDigit) latinSmallSupplement)
  assert "latin small latters supplement   - primToUpper        " (primStringEquality latinCapitalSupplement (mapString primToUpper latinSmallSupplement))
  assert "latin small latters supplement   - primToLower        " (primStringEquality latinSmallSupplement (mapString primToLower latinSmallSupplement))
  assert "latin small latters supplement   - primCharToNat      " (listNatEquality latinSmallSupplementCodes (map primCharToNat (primStringToList latinSmallSupplement)))
  assert "latin small latters supplement   - primNatToChar      " (primStringEquality latinSmallSupplement (primStringFromList (map primNatToChar latinSmallSupplementCodes)))

  -- latin capital letters supplement
  assert "latin capital latters supplement - not primIsLower    " (allString (not ∘ primIsLower) latinCapitalSupplement)
  assert "latin capital latters supplement - not primIsDigit    " (allString (not ∘ primIsDigit) latinCapitalSupplement)
  assert "latin capital latters supplement - primIsAlpha        " (allString primIsAlpha latinCapitalSupplement)
  assert "latin capital latters supplement - not primIsSpace    " (allString (not ∘ primIsSpace) latinCapitalSupplement)
  assert "latin capital latters supplement - not primIsAscii    " (allString (not ∘ primIsAscii) latinCapitalSupplement)
  assert "latin capital latters supplement - primIsLatin1       " (allString primIsLatin1 latinCapitalSupplement)
  assert "latin capital latters supplement - primIsPrint        " (allString primIsPrint latinCapitalSupplement)
  assert "latin capital latters supplement - not primIsHexDigit " (allString (not ∘ primIsHexDigit) latinCapitalSupplement)
  assert "latin capital latters supplement - primToUpper        " (primStringEquality latinCapitalSupplement (mapString primToUpper latinCapitalSupplement))
  assert "latin capital latters supplement - primToLower        " (primStringEquality latinSmallSupplement (mapString primToLower latinCapitalSupplement))
  assert "latin capital latters supplement - primCharToNat      " (listNatEquality latinCapitalSupplementCodes (map primCharToNat (primStringToList latinCapitalSupplement)))
  assert "latin capital latters supplement - primNatToChar      " (primStringEquality latinCapitalSupplement (primStringFromList (map primNatToChar latinCapitalSupplementCodes)))

  -- circled latin small letters
  assert "circled latin small letters      - not primIsLower    " (allString (not ∘ primIsLower) circledLatinSmallLetter)
  assert "circled latin small letters      - not primIsDigit    " (allString (not ∘ primIsDigit) circledLatinSmallLetter)
  assert "circled latin small letters      - not primIsAlpha    " (allString (not ∘ primIsAlpha) circledLatinSmallLetter)
  assert "circled latin small letters      - not primIsSpace    " (allString (not ∘ primIsSpace) circledLatinSmallLetter)
  assert "circled latin small letters      - not primIsAscii    " (allString (not ∘ primIsAscii) circledLatinSmallLetter)
  assert "circled latin small letters      - not primIsLatin1   " (allString (not ∘ primIsLatin1) circledLatinSmallLetter)
  assert "circled latin small letters      - primIsPrint        " (allString primIsPrint circledLatinSmallLetter)
  assert "circled latin small letters      - not primIsHexDigit " (allString (not ∘ primIsHexDigit) circledLatinSmallLetter)
  assert "circled latin small letters      - primToUpper        " (primStringEquality circledLatinCapitalLetter (mapString primToUpper circledLatinSmallLetter))
  assert "circled latin small letters      - primToLower        " (primStringEquality circledLatinSmallLetter (mapString primToLower circledLatinSmallLetter))
  assert "circled latin small letters      - primCharToNat      " (listNatEquality circledLatinSmallLetterCodes (map primCharToNat (primStringToList circledLatinSmallLetter)))
  assert "circled latin small letters      - primNatToChar      " (primStringEquality circledLatinSmallLetter (primStringFromList (map primNatToChar circledLatinSmallLetterCodes)))

  -- circled latin capital letters
  assert "circled latin capital letters    - not primIsLower    " (allString (not ∘ primIsLower) circledLatinCapitalLetter)
  assert "circled latin capital letters    - not primIsDigit    " (allString (not ∘ primIsDigit) circledLatinCapitalLetter)
  assert "circled latin capital letters    - not primIsAlpha    " (allString (not ∘ primIsAlpha) circledLatinCapitalLetter)
  assert "circled latin capital letters    - not primIsSpace    " (allString (not ∘ primIsSpace) circledLatinCapitalLetter)
  assert "circled latin capital letters    - not primIsAscii    " (allString (not ∘ primIsAscii) circledLatinCapitalLetter)
  assert "circled latin capital letters    - not primIsLatin1   " (allString (not ∘ primIsLatin1) circledLatinCapitalLetter)
  assert "circled latin capital letters    - primIsPrint        " (allString primIsPrint circledLatinCapitalLetter)
  assert "circled latin capital letters    - not primIsHexDigit " (allString (not ∘ primIsHexDigit) circledLatinCapitalLetter)
  assert "circled latin capital letters    - primToUpper        " (primStringEquality circledLatinCapitalLetter (mapString primToUpper circledLatinCapitalLetter))
  assert "circled latin capital letters    - primToLower        " (primStringEquality circledLatinSmallLetter (mapString primToLower circledLatinCapitalLetter))
  assert "circled latin capital letters    - primCharToNat      " (listNatEquality circledLatinCapitalLetterCodes (map primCharToNat (primStringToList circledLatinCapitalLetter)))
  assert "circled latin capital letters    - primNatToChar      " (primStringEquality circledLatinCapitalLetter (primStringFromList (map primNatToChar circledLatinCapitalLetterCodes)))

  -- cjk unified ideographs
  assert "cjk unified ideographs           - not primIsLower    " (allString (not ∘ primIsLower) cjkUnified)
  assert "cjk unified ideographs           - not primIsDigit    " (allString (not ∘ primIsDigit) cjkUnified)
  assert "cjk unified ideographs           - primIsAlpha        " (allString primIsAlpha cjkUnified)
  assert "cjk unified ideographs           - not primIsSpace    " (allString (not ∘ primIsSpace) cjkUnified)
  assert "cjk unified ideographs           - not primIsAscii    " (allString (not ∘ primIsAscii) cjkUnified)
  assert "cjk unified ideographs           - not primIsLatin1   " (allString (not ∘ primIsLatin1) cjkUnified)
  assert "cjk unified ideographs           - primIsPrint        " (allString primIsPrint cjkUnified)
  assert "cjk unified ideographs           - not primIsHexDigit " (allString (not ∘ primIsHexDigit) cjkUnified)
  assert "cjk unified ideographs           - primToUpper        " (primStringEquality cjkUnified (mapString primToUpper cjkUnified))
  assert "cjk unified ideographs           - primToLower        " (primStringEquality cjkUnified (mapString primToLower cjkUnified))
  assert "cjk unified ideographs           - primCharToNat      " (listNatEquality cjkUnifiedCodes (map primCharToNat (primStringToList cjkUnified)))
  assert "cjk unified ideographs           - primNatToChar      " (primStringEquality cjkUnified (primStringFromList (map primNatToChar cjkUnifiedCodes)))
