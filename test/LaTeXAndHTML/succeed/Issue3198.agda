-- If a symbolic identifier is generated for a comment, then the
-- comment starts with the symbol @.

module Issue3198 where

-- @ A definition.

postulate
  A : Set

-- @ A private definition.

private postulate
  B : Set

-- @ Another definition.

-- With an extra comment.

postulate
  C : Set

-- @ A data type.

data D : Set

-- There is no symbolic identifier for this comment, because D is
-- declared above.

data D where

-- There is also no symbolic identifier for this comment, because…

private -- …the following comment is preceded by another token on the
        -- same line (and consecutive comments with the same
        -- indentation are treated as one comment).
  postulate E : Set

private -- However, there is a symbolic identifier for the following
        -- comment,

  -- @ because that comment uses a different indentation.

  postulate F : Set

private -- Again there is a symbolic identifier for the following
        -- comment,

           -- @ because that comment uses a different indentation.

  postulate G : Set

private {- A comment. -} {- Another comment. -}

        -- @ There is a symbolic identifier for this comment, because
        -- the previous comment uses a different indentation.

  postulate H : Set

private {- No symbolic identifier here -} {- or here. -}

  postulate I : Set

{- @ This kind of comment -} {- can be used. -}

postulate J : Set → Set

-- Pragmas do not count as comments.

{-# BUILTIN IO J #-}

postulate K : Set

-- Fixity declarations are not ignored.

infix 0 !_

postulate !_ : Set → Set

postulate
  -- @ The modalities @0,
  @0 L : Set

  -- @ @ω,
  @ω M : Set

  -- @ @erased,
  @erased N : Set

  -- @ ".",
  .O : Set

  -- @ and @(tactic f) can be used.
  @(tactic f) P : Set
