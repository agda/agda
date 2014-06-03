{-# OPTIONS_GHC -w -fwarn-incomplete-patterns -Werror #-}
module Syntax.Abstract where

import Data.String (IsString(fromString))
import Data.Typeable (Typeable)

data SrcLoc = SrcLoc { pLine :: Int, pCol :: Int }

noSrcLoc = SrcLoc 0 0

instance Show SrcLoc where
  show (SrcLoc line col) = concat [show line, ":", show col]

data Name = Name { nameLoc :: SrcLoc, nameString :: String }
    deriving (Typeable)

name :: String -> Name
name s = Name noSrcLoc s

instance IsString Name where
  fromString = name

instance Eq Name where
  Name _ x == Name _ y = x == y

instance Ord Name where
  Name _ x `compare` Name _ y = compare x y

data Decl = TypeSig TypeSig
          | FunDef  Name [Pattern] Expr
          | DataDef Name [Name] [TypeSig]
          | RecDef  Name [Name] Name [TypeSig]

data TypeSig = Sig { typeSigName :: Name
                   , typeSigType :: Expr
                   }

data Expr = Lam Name Expr
          | Pi Name Expr Expr
          | Fun Expr Expr
          | Equal Expr Expr Expr
          | App Head [Elim]
          | Set SrcLoc
          | Meta SrcLoc
          | Refl SrcLoc
          | Con Name [Expr]

data Head = Var Name
          | Def Name
          | J SrcLoc

data Elim = Apply Expr
          | Proj Name
  deriving Eq

data Pattern = VarP Name
             | WildP SrcLoc
             | ConP Name [Pattern]

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Name where
  srcLoc (Name p _) = p

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
    FunDef x _ _   -> srcLoc x
    DataDef x _ _  -> srcLoc x
    RecDef x _ _ _ -> srcLoc x

instance HasSrcLoc TypeSig where
  srcLoc (Sig x _) = srcLoc x

instance HasSrcLoc Expr where
  srcLoc e = case e of
    Lam x _     -> srcLoc x
    Pi x _ _    -> srcLoc x
    Fun a _     -> srcLoc a
    Equal _ a _ -> srcLoc a
    App h _     -> srcLoc h
    Set p       -> p
    Meta p      -> p
    Con c _     -> srcLoc c
    Refl p      -> p

instance HasSrcLoc Head where
  srcLoc h = case h of
    Var x    -> srcLoc x
    Def x    -> srcLoc x
    J loc    -> loc

instance HasSrcLoc Pattern where
  srcLoc p = case p of
    WildP p  -> p
    VarP x   -> srcLoc x
    ConP c _ -> srcLoc c

instance HasSrcLoc Elim where
  srcLoc e = case e of
    Apply e -> srcLoc e
    Proj x  -> srcLoc x

-- | Syntactic equality (ignoring source locations).

instance Eq Expr where
  Lam x e     == Lam x' e'      = x == x' && e == e'
  Pi x a b    == Pi x' a' b'    = x == x' && a == a' && b == b'
  Fun a b     == Fun a' b'      = a == a' && b == b'
  Equal a x y == Equal a' x' y' = a == a' && x == x' && y == y'
  App h es    == App h' es'     = h == h' && es == es'
  Set _       == Set _          = True
  Meta _      == Meta _         = True
  _           == _              = False

instance Eq Head where
  Var x  == Var x' = x == x'
  Def f  == Def f' = f == f'
  J _    == J _    = True
  _      == _      = False
