{-# OPTIONS_GHC -Wunused-imports #-}

-- | ASTs for subset of GHC Haskell syntax.

module Agda.Utils.Haskell.Syntax where

import Data.Text (Text)

-- * Modules

data Module = Module ModuleName [ModulePragma] [ImportDecl] [Decl]

data ModulePragma
  = LanguagePragma [Name]
  | OtherPragma String  -- ^ Unstructured pragma (Andreas, 2017-08-23, issue #2712).

data ImportDecl = ImportDecl
  { importModule    :: ModuleName
  , importQualified :: Bool
  , importSpecs     :: Maybe (Bool, [ImportSpec])
  }

data ImportSpec = IVar Name

-- * Declarations

data Decl = TypeDecl Name [TyVarBind] Type
          | DataDecl DataOrNew Name [TyVarBind] [ConDecl] [Deriving]
          | TypeSig [Name] Type
          | FunBind [Match]
            -- ^ Should not be used when 'LocalBind' could be used.
          | LocalBind Strictness Name Rhs
            -- ^ Should only be used in @let@ or @where@.
          | PatSyn Pat Pat
          | FakeDecl String
          | Comment String
  deriving (Eq)

data DataOrNew = DataType | NewType
  deriving (Eq)

data ConDecl = ConDecl Name [(Maybe Strictness, Type)]
  deriving (Eq)

data Strictness = Lazy | Strict
  deriving (Eq)

type Deriving = (QName, [Type])

data Binds = BDecls [Decl]
  deriving (Eq)

data Rhs = UnGuardedRhs Exp
         | GuardedRhss [GuardedRhs]
  deriving (Eq)

data GuardedRhs = GuardedRhs [Stmt] Exp
  deriving (Eq)

data Match = Match Name [Pat] Rhs (Maybe Binds)
  deriving (Eq)

-- * Expressions

data Type = TyForall [TyVarBind] Type
          | TyFun Type Type
          | TyCon QName
          | TyVar Name
          | TyApp Type Type
          | FakeType String
  deriving (Eq)

data Pat = PVar Name
         | PLit Literal
         | PAsPat Name Pat
         | PWildCard
         | PBangPat Pat
         | PApp QName [Pat]
         | PatTypeSig Pat Type
         | PIrrPat Pat
  deriving (Eq)


data Stmt = Qualifier Exp
          | Generator Pat Exp
  deriving (Eq)

data Exp = Var QName
         | Con QName
         | Lit Literal
         | InfixApp Exp QOp Exp
         | Ann Exp Type
         | App Exp Exp
         | Lambda [Pat] Exp
         | Let Binds Exp
         | If Exp Exp Exp
         | Case Exp [Alt]
         | ExpTypeSig Exp Type
         | NegApp Exp
         | FakeExp String
  deriving (Eq)

data Alt = Alt Pat Rhs (Maybe Binds)
  deriving (Eq)

data Literal = Int Integer | Frac Rational | Char Char | String Text
  deriving (Eq)

-- * Names

data ModuleName = ModuleName String
  deriving (Eq, Ord)

data QName = Qual ModuleName Name | UnQual Name
  deriving (Eq)

data Name = Ident String | Symbol String
  deriving (Eq)

data QOp = QVarOp QName
  deriving (Eq)

data TyVarBind = UnkindedVar Name
  deriving (Eq)

unit_con :: Exp
unit_con = Con (UnQual (Ident "()"))
