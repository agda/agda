{-# OPTIONS -v interaction.case:40 #-}
-- Andreas, 2025-05-07, issue #7863
-- Catch error when case splitting on ill-formed variables

open import Agda.Builtin.Bool

uu : Bool → Bool
uu x = {! __ !}  -- C-c C-c

-- error: [Interaction.CaseSplitError]
-- a name cannot contain two consecutive underscores

num : Bool → Bool
num x = {! 42 !}  -- C-c C-c

-- error: [Interaction.CaseSplitError]
-- in the name 42, the part 42 is not valid because it is a literal

semi : Bool → Bool
semi x = {! ; !}  -- C-c C-c

-- error: [Interaction.CaseSplitError]
-- in the name ;, the part ; is not valid because it is used to separate declarations

par : Bool → Bool
par x = {! (x) !}  -- C-c C-c

-- error: [Interaction.CaseSplitError]
-- in the name (x), the part (x) is not valid because it is used to parenthesize expressions

dd : Bool → Bool
dd x = {! ..!}

-- error: [Interaction.CaseSplitError]
-- in the name .., the part .. is not valid because it is a modality

pragma  : Bool → Bool
pragma x = {! {-#!}

-- error: [Interaction.CaseSplitError]
-- in the name {-#, the part {-# is not valid because it is used for pragmas

qual : Bool → Bool
qual x = {! M.d!}

-- error: [Interaction.CaseSplitError]
-- in the name M.d, the part M.d is not valid because it is qualified

str : Bool → Bool
str x = {! "x"!}

-- error: [Interaction.CaseSplitError]
-- in the name "x", the part "x" is not valid because it is a literal

con : Bool → Bool
con x = {! constructor !}

-- error: [Interaction.CaseSplitError]
-- in the name constructor, the part constructor is not valid because it is a keyword
