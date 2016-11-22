
module Agda.Utils.Haskell.Syntax where

import Data.Void

type SrcLoc = Void

-- Modules --

data Module = Module SrcLoc ModuleName [ModulePragma]
                     (Maybe Void) (Maybe Void) [ImportDecl] [Decl]

data ModulePragma = LanguagePragma SrcLoc [Name]

data ImportDecl = ImportDecl
      { importLoc       :: SrcLoc
      , importModule    :: ModuleName
      , importQualified :: Bool
      , importSrc       :: Bool
      , importSafe      :: Bool
      , importPkg       :: Maybe Void
      , importAs        :: Maybe Void
      , importSpecs     :: Maybe (Bool, [ImportSpec]) }

data ImportSpec = IVar Name

-- Declarations --

data Decl = TypeDecl SrcLoc Name [TyVarBind] Type
          | DataDecl SrcLoc DataOrNew [Void] Name [TyVarBind] [QualConDecl] [Deriving]
          | TypeSig  SrcLoc [Name] Type
          | PatBind  SrcLoc Pat Rhs (Maybe Binds)
          | FunBind [Match]
  deriving (Eq)

data DataOrNew = DataType | NewType
  deriving (Eq)

data QualConDecl = QualConDecl SrcLoc [Void] [Void] ConDecl
  deriving (Eq)

data ConDecl = ConDecl Name [Type]
  deriving (Eq)

type Deriving = (QName, [Type])

data Binds = BDecls [Decl]
  deriving (Eq)

data Sign = Signless
  deriving (Eq)

data Rhs = UnGuardedRhs Exp
         | GuardedRhss [GuardedRhs]
  deriving (Eq)

data GuardedRhs = GuardedRhs SrcLoc [Stmt] Exp
  deriving (Eq)

data Match = Match SrcLoc Name [Pat] (Maybe Void) Rhs (Maybe Binds)
  deriving (Eq)

-- Expressions --

data Type = TyForall (Maybe [TyVarBind]) [Void] Type
          | TyFun Type Type
          | TyCon QName
          | TyVar Name
          | TyApp Type Type
  deriving (Eq)

data Pat = PVar Name
         | PLit Sign Literal
         | PAsPat Name Pat
         | PWildCard
         | PBangPat Pat
         | PApp QName [Pat]
         | PatTypeSig SrcLoc Pat Type
         | PIrrPat Pat
  deriving (Eq)


data Stmt = Qualifier Exp
          | Generator SrcLoc Pat Exp
  deriving (Eq)

data Exp = Var QName
         | Con QName
         | Lit Literal
         | InfixApp Exp QOp Exp
         | App Exp Exp
         | Lambda SrcLoc [Pat] Exp
         | Let Binds Exp
         | If Exp Exp Exp
         | Case Exp [Alt]
         | ExpTypeSig SrcLoc Exp Type
         | NegApp Exp
  deriving (Eq)

data Alt = Alt SrcLoc Pat Rhs (Maybe Binds)
  deriving (Eq)

data Literal = Int Integer | Frac Rational | Char Char | String String
  deriving (Eq)

-- Names --

data ModuleName = ModuleName String
  deriving (Eq, Ord)

data QName = Qual ModuleName Name | UnQual Name | Special SpecialCon
  deriving (Eq)

data Name = Ident String | Symbol String
  deriving (Eq)

data QOp = QVarOp QName | QConOp QName
  deriving (Eq)

data TyVarBind = UnkindedVar Name
  deriving (Eq)

data SpecialCon = UnitCon
  deriving (Eq)

unit_con :: Exp
unit_con = Con (Special UnitCon)
