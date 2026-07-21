{-# OPTIONS --without-K --safe #-}

module _ where

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

-- Checking Issue8626
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: __IMPOSSIBLE__, called at src/full/Agda/TypeChecking/CompiledClause/Compile.hs:180:20 in Agda-2.9.0-4LTCrYcgM18IOO7aOFG0rT:Agda.TypeChecking.CompiledClause.Compile%
--
-- Split tree:
--    split at {0}
--    |
--    +- M.Relevance.! -> done, 2 bindings
--    |
--    `- M.Relevance.% -> split at 0
--       |
--       `- M.Jdg.N -> split at 1
--          |
--          +- M.Prp.ps -> lazy split at 0
--          |  |
--          |  `- M.Term.suc -> split at 2
--          |     |
--          |     `- M.Jdg.N -> split at 3
--          |        |
--          |        +- M.Prp.ps -> lazy split at 2
--          |        |  |
--          |        |  `- M.Term.suc -> done, 2 bindings
--          |        |
--          |        `- M.Prp.pz -> done, 1 bindings
--          |
--          `- M.Prp.pz -> split at 1
--             |
--             `- M.Jdg.N -> split at 2
--                |
--                +- M.Prp.ps -> lazy split at 1
--                |  |
--                |  `- M.Term.suc -> done, 1 bindings
--                |
--                `- M.Prp.pz -> done, 0 bindings
--
--    covering patterns for M.natrec-congTerm
--      [{rF = !}, v, w]
--      [{rF = %}, N (suc m) (ps m), N (suc l) (ps n)]
--      [{rF = %}, N (suc m) (ps m), N j pz]
--      [{rF = %}, N n pz, N (suc c) (ps n)]
--      [{rF = %}, N n pz, N h pz]
--
-- Compiled case trees:
--    compiled clauses of  natrec-congTerm  (still containing record splits)
--      case {0} of
--        M.Relevance.! -> done 0?Rec: [v, w] M.tt
--        _ -> case 1 of
--               M.Jdg.N ->
--                 case 2 of
--                   M.Prp.ps ->
--                     case 3 of
--                       M.Jdg.N -> case 4 of M.Prp.pz -> done 1?Rec: [{_}, _, _, _] M.tt
--
--                                  Note: after this `case 4 of M.Prop.pz` split, the clauses are
--                                      M.Prp.pz ->
--                                        [1: [{_}, ~M.Term.suc m, .@2, .M.Term.zero] -> M.tt,
--                                         2: [{_}, _, _, .M.Term.zero] -> M.tt]
--
--
--                       _ -> case 1 of ~ M.Term.suc -> done 3?Rec: [{_}, m, _, l] M.tt
--                   _ -> case 3 of
--                          M.Jdg.N -> case 4 of M.Prp.pz -> done 2?Rec: [{_}, _, _, _] M.tt
--               _ -> case 2 of
--                      M.Jdg.N -> case 3 of M.Prp.pz -> done 2?Rec: [{_}, q, _] M.tt
--                      _ -> done 4?Rec: [{_}, b, c] M.tt
