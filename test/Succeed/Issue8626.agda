{-# OPTIONS --without-K --safe #-}
-- {-# OPTIONS -v tc.cover:10 #-}

module Issue8626 where

record Unit : Set where constructor tt

data Relevance : Set where
  ! % : Relevance

data Term : Set where
  zero : Term
  suc  : Term → Term

data Prp : Term → Set where
  ps : (n : Term) → Prp (suc n)
  pz : Prp zero

data Jdg : Set where
  N : (n : Term) (prop : Prp n) → Jdg

natrec-congTerm : {rF : Relevance} → Jdg → Jdg → Unit
natrec-congTerm {rF = !} v            w        = tt
natrec-congTerm          (N i (ps m)) (N j pz) = tt
natrec-congTerm          q            (N h pz) = tt
natrec-congTerm          (N k (ps m)) l        = tt
natrec-congTerm          b            c        = tt

-- Error was:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: __IMPOSSIBLE__, called at src/full/Agda/TypeChecking/CompiledClause/Compile.hs:180:20
--
-- Split tree:
--    split at {0}
--    |
--    +- Relevance.! -> done, 2 bindings
--    |
--    `- Relevance.% -> split at 0
--       |
--       `- Jdg.N -> split at 1
--          |
--          +- Prp.ps -> lazy split at 0
--          |  |
--          |  `- Term.suc -> split at 2
--          |     |
--          |     `- Jdg.N -> split at 3
--          |        |
--          |        +- Prp.ps -> lazy split at 2
--          |        |  |
--          |        |  `- Term.suc -> done, 2 bindings
--          |        |
--          |        `- Prp.pz -> done, 1 bindings
--          |
--          `- Prp.pz -> split at 1
--             |
--             `- Jdg.N -> split at 2
--                |
--                +- Prp.ps -> lazy split at 1
--                |  |
--                |  `- Term.suc -> done, 1 bindings
--                |
--                `- Prp.pz -> done, 0 bindings
--
--    covering patterns for natrec-congTerm
--      [{rF = !}, v, w]
--      [{rF = %}, N (suc m) (ps m), N (suc l) (ps n)]
--      [{rF = %}, N (suc m) (ps m), N j pz]
--      [{rF = %}, N n pz, N (suc c) (ps n)]
--      [{rF = %}, N n pz, N h pz]
--
-- Compiled case trees:
--    compiled clauses of  natrec-congTerm  (still containing record splits)
--      case {0} of
--        Relevance.! -> done 0?Rec: [v, w] tt
--        _ -> case 1 of
--               Jdg.N ->
--                 case 2 of
--                   Prp.ps ->
--                     case 3 of
--                       Jdg.N -> case 4 of Prp.pz -> done 1?Rec: [{_}, _, _, _] tt
--
--                                  Note: after this `case 4 of Prop.pz` split, the clauses are
--                                      Prp.pz ->
--                                        [1: [{_}, ~Term.suc m, .@2, .Term.zero] -> tt,
--                                         2: [{_}, _, _, .Term.zero] -> tt]
--
--
--                       _ -> case 1 of ~ Term.suc -> done 3?Rec: [{_}, m, _, l] tt
--                   _ -> case 3 of
--                          Jdg.N -> case 4 of Prp.pz -> done 2?Rec: [{_}, _, _, _] tt
--               _ -> case 2 of
--                      Jdg.N -> case 3 of Prp.pz -> done 2?Rec: [{_}, q, _] tt
--                      _ -> done 4?Rec: [{_}, b, c] tt
