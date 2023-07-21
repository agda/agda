{-# OPTIONS_GHC -Wunused-imports #-}

------------------------------------------------------------------------
-- | Strictification of Haskell code
------------------------------------------------------------------------

module Agda.Compiler.MAlonzo.Strict where

import Agda.Utils.Haskell.Syntax

-- | The function 'makeStrict' makes every function argument, case and
-- generator pattern, and 'LocalBind' binding strict (except for those
-- patterns that are marked as irrefutable, and anything in a
-- 'FakeDecl' or 'FakeExp'). Note that only the outermost patterns are
-- made strict.

class MakeStrict a where
  makeStrict :: a -> a

instance MakeStrict a => MakeStrict [a] where
  makeStrict = map makeStrict

instance MakeStrict a => MakeStrict (Maybe a) where
  makeStrict = fmap makeStrict

instance MakeStrict Module where
  makeStrict (Module m pragmas imps decls) =
    Module m pragmas imps (makeStrict decls)

instance MakeStrict Decl where
  makeStrict = \case
    d@TypeDecl{}      -> d
    d@DataDecl{}      -> d
    d@TypeSig{}       -> d
    FunBind ms        -> FunBind (makeStrict ms)
    LocalBind s f rhs -> LocalBind Strict f (makeStrict rhs)
    d@PatSyn{}        -> d
    d@FakeDecl{}      -> d
    d@Comment{}       -> d

instance MakeStrict Match where
  makeStrict (Match f ps rhs wh) =
    Match f (makeStrict ps) (makeStrict rhs) (makeStrict wh)

instance MakeStrict Pat where
  makeStrict = \case
    p@PVar{}       -> PBangPat p
    p@PLit{}       -> PBangPat p
    PAsPat x p     -> PAsPat x (makeStrict p)
    p@PWildCard{}  -> PBangPat p
    p@PBangPat{}   -> p
    p@PApp{}       -> PBangPat p
    PatTypeSig p t -> PatTypeSig (makeStrict p) t
    p@PIrrPat{}    -> p

instance MakeStrict Binds where
  makeStrict (BDecls ds) = BDecls (makeStrict ds)

instance MakeStrict Rhs where
  makeStrict (UnGuardedRhs e) = UnGuardedRhs (makeStrict e)
  makeStrict (GuardedRhss rs) = GuardedRhss (makeStrict rs)

instance MakeStrict GuardedRhs where
  makeStrict (GuardedRhs ss e) =
    GuardedRhs (makeStrict ss) (makeStrict e)

instance MakeStrict Stmt where
  makeStrict = \case
    Qualifier e   -> Qualifier (makeStrict e)
    Generator p e -> Generator (makeStrict p) (makeStrict e)

instance MakeStrict Exp where
  makeStrict e =
    case e of
      Var{}           -> e
      Con{}           -> e
      Lit{}           -> e
      InfixApp a op b -> InfixApp (makeStrict a) op (makeStrict b)
      Ann e ty        -> Ann (makeStrict e) ty
      App a b         -> App (makeStrict a) (makeStrict b)
      Lambda ps e     -> Lambda (makeStrict ps) (makeStrict e)
      Let bs e        -> Let (makeStrict bs) (makeStrict e)
      If a b c        -> If (makeStrict a) (makeStrict b) (makeStrict c)
      Case e bs       -> Case (makeStrict e) (makeStrict bs)
      ExpTypeSig e t  -> ExpTypeSig (makeStrict e) t
      NegApp e        -> NegApp (makeStrict e)
      FakeExp s       -> FakeExp s

instance MakeStrict Alt where
  makeStrict (Alt pat rhs wh) =
    Alt (makeStrict pat) (makeStrict rhs) (makeStrict wh)
