{-|

  Predifined fast strings.

-}
module PreStrings(
  preStrTable,
  fsEmpty, fsUnderscore, fsBOX, fsQuest, fsRec, fsNoMatch, fsTmp, fsCName, fsStringMod,    fsString, fsIntMod,  fsInt, fsCharMod, fsChar,  fsBool, fsTrue,

 fsFalse, fsRational,fsMonad,fsBind, fsBind_, fsReturn, fsFail,fsStar, fsComma, fsRArrow, fsBRArrow,  fsImpl,fsImpossible, fsList, fsNil, fsCons, fsIntegerMod, fsInteger,  fsInternalHypvar,fsHypvar,fsVar, fsVar1, fsVar2,fsVar3, fsTypeVar,fsSetoid,fsElem,fsEqual,fsRef, fsSym, fsTran,fsEl,fsEq,fsHypTypeVar,fsHypTypeVar, fsHypTypeVarB, fsListVarHead, fsListVarTail, fsMonadName, fsJM, fsSame, fsVara, fsVarb, fsPair
) where

import AgdaScans(mapAccumL)
import FString(FString, StrTable, hmkFString, emptyStrTable)

preStrTable :: StrTable

fsEmpty, fsUnderscore, fsBOX, fsQuest, fsRec, fsNoMatch, fsTmp, fsCName, fsStringMod,    fsString, fsIntMod,  fsInt, fsCharMod, fsChar, fsBool, fsTrue,
 fsFalse, fsRational,fsMonad,fsBind, fsBind_, fsReturn, fsFail,fsStar, fsComma, fsRArrow, fsBRArrow,  fsImpl,fsImpossible, fsList, fsNil, fsCons, fsIntegerMod, fsInteger,  fsInternalHypvar,fsHypvar,fsVar, fsVar1, fsVar2,fsVar3, fsTypeVar,fsSetoid,fsElem,fsEqual,fsRef, fsSym, fsTran,fsEl,fsEq,fsDummyValue,fsHypTypeVar, fsHypTypeVarB, fsListVarHead, fsListVarTail, fsMonadName, fsJM, fsSame,fsVara,fsVarb, fsPair :: FString



(preStrTable, [
  fsEmpty, fsUnderscore, fsBOX, fsQuest, fsRec, fsNoMatch,
  fsTmp, fsCName, fsStringMod,    fsString, fsIntMod,
  fsInt, fsCharMod, fsChar,  fsBool, fsTrue,
  fsFalse, fsRational,fsMonad,fsBind, fsBind_,
  fsReturn,fsFail,fsStar, fsComma, fsRArrow,
  fsBRArrow, fsImpl, fsImpossible, fsList, fsNil,
  fsCons, fsIntegerMod, fsInteger,fsInternalHypvar,fsHypvar,
  fsVar, fsVar1, fsVar2,fsVar3, fsTypeVar,
  fsSetoid,fsElem,fsEqual,fsRef, fsSym,
  fsTran,fsEl,fsEq,fsDummyValue,fsHypTypeVar,
  fsHypTypeVarB, fsListVarHead, fsListVarTail, fsMonadName, fsJM,
  fsSame, fsVara, fsVarb, fsPair
  ]
 ) = mapAccumL hmkFString emptyStrTable
 ["",      "_",          "%BOX","?"    , "_r",  "%noMatch",
  "%","%c","System$String","String","System$Int",
  "Int", "System$Char", "Char",  "Bool", "True",
  "False", "Rational", "Monad",">>=", ">>",
  "return", "fail",  "*",    ",",     "->",
  "|->", "=>",    "%impossible", "List", "Nil",
  ":", "System$Integer", "Integer", "%h", "h",
  "x", "x1", "x2","x3","X",
  "Setoid","Elem","Equal","ref","sym",
  "tran","El","Eq", "_V", "A",
  "B", "x", "xs", "m","JMeq",
  "same", "a", "b", "\215"  -- \215 == ×
 ]
