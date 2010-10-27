{-# OPTIONS -cpp #-}
#include "config.h"
-- | Error codes and error messages
module Error(EMsg, ErrMsg(..), PassMsg(..),prEMsg, prError, eMany,eMsg,isPassMsg) where
import Position
import Util(unwordsWith)
import PPrint
import Data.List(intersperse)

type EMsg = (Position, ErrMsg)

data PassMsg                          -- errors that will be handled somewhere else
        = EGetSort
        | ESplitSig
        | ESplitStruct
        | ESplitPackage
        | ESplitFun
        | ESplitMeta
        | ESplitData
        | ESplitSort
        | ESplitCon
        | ESplitStop
        | ENoArity
        | ENotEqual
        | ELookupProj
        | ENotInSig
        | EMissingRecField
        | ENoSolve
        | EImitate
        | ETooManyArgsCon
        | ETooMany
        | ETooFew
        | EProjImpossible
        | ETermProblem String
       | ENotInDef
     deriving (Show,Eq)

{-
data Warning =
      WNotTerminate String
    | WNotPositive String
-}




data ErrMsg
        = ESyntax String [String]       -- found token, expected tokens
        | EBadCharLit
        | EBadStringLit
        | EBadLexChar Char
        | EUntermComm Position
        | EMissingNL
        | EUnbound String

        | EDuplicate Position String
        | EDuplicateCon String
{-10-}  | ETypeError String String String String String Position
        | EKindError String String String String Position
--      | ETypeTermination String String
--      | EFieldNonKind String String
--      | EConNonKind String String
--      | EVarNonKind String String
        | ENotSum String
        | ENotSumElem String String
        | ENotProduct String String
        | ENotProductOpen
 {-20-} | ENotProductElem String String
        | ENotSumCase String String
        | ENotInType String String
--      | ENoSign String
--      | EBadRecursion String
        | ETermination String String
--         | EHide Bool String
--      | ENoHide String
        | EOverlap
        | EBadPatterns String
 {-30-} | EMissingPatArg String
--         | EExtraPatArg String
--      | ENoArms String
        | ETooManyArgs String
--      | EVaryingArgs String
--      | EVaryingHiddenArgs String
--      | ENoSignature String
--      | ENotHidden
--      | ENotProductCoerce String String
--      | ENotProductCoerceT String String
{-40-}  --  | ENoCoerce String String
        | ENotInRecord String String Position
        | EMany [EMsg]
        | ETEMP String

-- {-1-}        | WNoMatch
--      | WBoundConstr String
        | EConflictingModifiers String String
        | EUntermMeta Position
{-50-}        | EUninstantiated String
        | EUnknownConstraint String
        | EUnknownTactic String
        | ESolveNotApp String String
        | ESolveNonTerm Int
        | ECommand String
        | EInternal String
        | EPass PassMsg
        | EParseCommand String [String]
        | ENotType String String
        | ENotFunction
        | EInLetDef String String String
        | ERefineArity String
        | ERefine Int
        | ENotFun String String
        | ENotEqualValues String Position String
        | EDeclaredNotEqual String String String String
        | ENotEqualConstraints String String
        | ENotSignature String
        | ECanNotInferType String
        | EMissingField String Position
        | ETooManyFields String Position
        | EMisMatchingTypes String String String Position
        | ENotStruct String
        | ENotSetData
        | ENotTypeSig
        | WNotTerminate String
        | WNotPositive [String] String
       --  | WUnknownDataPos String
        --  | WMutual [String]
        --  | Warnings [EMsg]
        | EMissingConstrs [String]
        | ENrConstrArgs String Int
        | EPatternNotConstr
        | EPatternNested
        | ENoMeta
        | ENoOpenInMutual
        | EWrongPlace String
        | ENoFile String
        | ENoOpen
        | EBecause ErrMsg [EMsg]
        | EHiddenArgs
        | ENotClass String
        | EClassTooMany String
        | EClassNotVarArg String
        | ENoInstance String String
        | EIfNotBool String
        | ELookupPrelude String
        | ELastInDo
        | ENoSuchPlugin String
        | EPluginError String       -- ^ Error message for plugin
       deriving (Eq)


instance Show ErrMsg where
--    showsType _ = showString "Errmsg"
    showsPrec _ e = showString "ErrMsg:" . showString (prError e)

instance PPrint ErrMsg where
    pPrint _ _ e = text (show e)


prEMsg (p,m) = let s = prPosition p
               in if null s
                     then prError m
                     else "At: "++s++"\n"++prError m
-- 1
prError (ESyntax s ss)                 = "Syntax error: found token "++s++
                                         if null ss then "" else ", expected "++unwordsOr ss
prError EBadCharLit                    = "Bad Char CSynliteral"
prError EBadStringLit                  = "Bad String literal"
prError (EBadLexChar c)                = "Bad character in input: "++show c
prError (EUntermComm p)                = "Unterminated {- comment, started at "++prPosition p
                                                       -- -}
prError EMissingNL                     = "Missing new line after -- comment"
prError (EUnbound i)                   = "Undefined identifier: "++ishow i
prError (EConflictingModifiers s1 s2)  = "Conflicting modifiers: "++s1++" and "++s2
prError (EDuplicate p i)               = "Duplicate definition of "++ishow i++", other definition at "++prPosition p
prError (EDuplicateCon i)              = "Duplicate constructor names: "++ishow i
prError (ETypeError s msg e t1 t2 pos) =
       "Type error: "++s++
       "\nExpression\n"++e++
       "  has type\n"++t1++
       "  but should have type that is equal to\n"++t2++"\n"++
       prPos "  from " pos ++ msg
prError (EKindError msg e t1 t2 pos) =
     "Sort error: "++"\n"++
       e++ "  has sort\n"++
       t1++"  which is not contained in\n "++
       t2++
       prPos "  from " pos ++ msg
-- prError (ETypeTermination e t) =
--     "Type error: Cannot normalize \n"++t
-- prError (EFieldNonKind t i) = "Field type illegal: "++ i ++" :: " ++ t
-- prError (EConNonKind t i) = "Constructor field type illegal: " ++ t
-- prError (EVarNonKind t i) = "Variable type illegal: " ++ i ++ " :: " ++ t
prError (ENotSum t)           = "Constructor type is not a data: " ++ t
prError (ENotSumElem i t)     = "Constructor type does not contain constructor: " ++ i ++ " in " ++ t
prError (ENotProduct t i)     = "Type of selection expression ( ."++i++" ) not a signature: " ++ t
prError ENotProductOpen       = "Open expression is neither a package nor of signature type"
prError (ENotProductElem t i) = "Signature\n"++t++"\ndoes not contain selector: " ++ i
prError (ENotSumCase t i)     = "Case inspection on a non-data type: " ++ t
prError (ENotInType t i)      = "Type does not contain constructor: " ++ i ++ " in " ++ t
-- prError (ENoSign i) = "Definition must have a (complete) type signature: " ++ i
-- prError (EBadRecursion e) = "Illegal recursion in definition: " ++ e
prError (ETermination e e') = "No termination in:\n" ++ e ++"\nLast evaluation was:\n"++e'
-- prError (EHide b e) = "Argument should " ++ (if b then "" else "not ") ++ "be hidden: " ++ e
-- prError (ENoHide i) = "Cannot figure out hidden argument: " ++ i
prError (EOverlap) = "Overlapping pattern"
prError (EBadPatterns e) = "Bad patterns: " ++ e
prError (EMissingPatArg i) = "Missing/excess arguments to pattern constructor: " ++ i
-- prError (EExtraPatArg i) = "Extra argument to pattern constructor: " ++ i
-- prError (ENoArms e) = "Cannot figure out type of empty case: " ++ e
prError (ETooManyArgs p) = "More function arguments than the function type specifies: " ++ p
-- prError (EVaryingArgs i) = "Varying number of arguments to function: " ++ i
-- prError (EVaryingHiddenArgs i) = "Varying hiding of arguments to function: " ++ i
-- prError (ENotHidden) = "Hiding marker on non-hidden argument"
-- prError (ENotProductCoerce e t) = "Expression not a product: " ++ e ++ ", has type " ++ t
-- prError (ENotProductCoerceT t' t) = "Type not a product: " ++ t ++ "= " ++ t'
-- prError (ENoCoerce t e) = "Impossible coercion: " ++ e ++ " :: " ++ t
prError (ENotInRecord i t pos) = "Selection expression ( ."++i++" ) not in record : " ++ t ++
   prPos "\nnear " pos
prError (EMany es) = "Many:\n" ++ unlines (map prEMsg es)
prError (ETEMP s) = s

-- prError (WNoMatch) = "Missing cases, pattern matching may fail"
-- prError (WBoundConstr i) = "Variable in pattern with same the name as a constructor: " ++ i
-- prError _ = internalError "Missing error message."
prError (EUntermMeta p)        = "Unterminated {! meta variable, started at "++prPosition p
prError (EUninstantiated s)    = "Meta variable ?"++s++" is already instantiated or does not exist"
prError (EUnknownConstraint n) = "There is no such constraint: "++n
prError (EUnknownTactic n)     = "Unknown tactic: "++n
prError (ESolveNotApp n c)     = "You can not apply solve tactic: "++n++" on constraint "++c
prError (ESolveNonTerm n)      = "Solve has not terminated after "++show n++" calls"
prError (ECommand s)           = "Not allowed at this point: "++s
prError (EInternal msg)        = "good error message not implemented yet: \n"++msg++"\n"
prError (EPass p)              = "Internal error  : uncaught exception "++show p
prError (EParseCommand msg ss) = "Command error: found "++ msg++
                                 if null ss then "" else ", expected "++unwordsOr ss
prError (ENotType e t)         = "The type of "++e++" is "++t++". The type should be a sort"
prError (EInLetDef c k msg)    = "Error in the "++k++" of "++c++" because:\n"++msg
prError (ERefineArity t)       = "Can not refine because the number of arguments needed for: \n"++ t ++ " is unknown"
prError (ERefine i)            = "Can not refine, eiher it is not type correct or it has more than "++show i++" arguments"
prError (ENotFun e t)          = "Type error :\n  Expression "++ e ++
                                 "\nis declared to have type \n"++t ++
                                 "\nwhich is not a function type"

prError (ENotEqualValues s1 pos s2)     = "Expression \n"++ s1++"\nis not equal to\n"++s2++
  prPos " at position" pos
prError (EDeclaredNotEqual x t1 t2 msg) = "Variable "++x++" is declared to have type:\n"++t1++"\nwhich is not equal to:\n"++t2++(if null msg then "" else "\nsince \n"++msg)
prError (ENotEqualConstraints c msg)    = "The constraint\n" ++ c ++ "\n is unsolvable"++(if null msg then "\n" else " since\n"++msg)
prError (ENotSignature t)               = "The type of the structure is\n"++t++"\nwhich is not a signature"
prError (ECanNotInferType t)            = "Can not infer the type of:\n"++t
prError (EMissingField c pos)           = "Field: "++c++" at "++prPosition pos++" is missing in the structure"
prError (EMisMatchingTypes c t msg pos) = "Type of "++c++" : \n"++t++" does not match with declared type near "++prPosition pos++(if null msg then "" else " since \n"++msg)
prError (ETooManyFields s pos)          = "The field: "++s++ " is not defined in the signature near: "++prPosition pos
prError (ENotStruct e)                  =  "Expression: "++e++" must reduce to a structure"
prError (ENotSetData)                   = "data must have kind: Set"
prError ENotTypeSig                     = "Type of signature must be a sort"
prError (WNotTerminate str)             = "The call: "++str++"\nmight lead to non-termination"
prError (WNotPositive strs str)         = "The function"++plural "" str++" "++unwordsx "or" strs
                ++ " might have         a negative occurence of "++str


--prError (WMutual ss) = "Can not control the correctness of mutual definitions. Have not checked "++unwordsx "and" ss
--prError (WUnknownDataPos s) = "Can not check positivity of "++s
--prError (Warnings es) = "Warnings:\n" ++ unlines (map prEMsg es)
prError (EMissingConstrs ss) = "Missing constructors in case: "++ unwordsx "and" ss
prError (ENrConstrArgs s i) = "Constructor: "++s++" needs "++(show i)++" arguments"
prError ELastInDo = "an expression must be last in a do-block"

prError EPatternNotConstr    = "Only constructors are allowed in pattern"
prError EPatternNested       = "Nested patterns are not allowed"
prError ENoMeta              = "Imported file must not contain meta variables"
prError ENoOpenInMutual      = "No open definition in mutual definitions"
prError (EWrongPlace s)      = "You can not make " ++s++ " here"
prError (ENoFile f)          = "No such file: "++f
prError ENoOpen              = "Can only open top level packages at this point"
prError (EBecause e ms)      = prError e ++ "Because:\n" ++ unlines (map prEMsg ms)
prError (EHiddenArgs)        = "Hidden arguments/parameters don't match"
prError (ENotClass s)        = s ++ " is not a class"
prError (EClassTooMany s)    = "Only one argument is allowed "++s
prError (EClassNotVarArg s)  = "Argument must be a variables, was: " ++ s
prError (ENoInstance s1 s2)  = s1 ++ " is not an instance of " ++ s2
prError (EIfNotBool s)       = "type of: " ++ s ++ " is not Bool"
prError (ELookupPrelude s)   = "Internal error, could not lookup prelude name: " ++ s
prError (ENoSuchPlugin s) = "No such plugin: " ++ s
prError (EPluginError s) = "Plugin error: " ++ s

prPos :: String -> Position -> String
prPos str pos =
  if pos /= noPosition then str ++ prPosition pos ++ "\n"
                       else ""


eMsg :: Position -> ErrMsg -> EMsg
eMsg p e = (p,e)


isPassMsg (_,EPass _) = True
isPassMsg _ = False

ishow :: String -> String
ishow s = "\"" ++ s ++ "\""

plural s  [_] = s
plural ""  _ = "s"
plural "y" _ = "ies"
plural "s" _ = "es"

unwordsAnd = unwordsx "and"
unwordsOr = unwordsx "or"

unwordsx _ [] = ""
unwordsx _ [x] = x
unwordsx s [x1, x2] = unwords [x1, s, x2]
unwordsx s xs = unwordsWith ", " (init xs++[s++" "++last xs])

eMany es = (noPosition, EMany es)

--eWarning es = (noPosition, Warnings es)
