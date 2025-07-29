primitive
  data D : Set where

-- Bad error message WAS:
-- A postulate block can only contain type signatures or instance blocks

-- Better error (#1698): Parse error

-- New error (PR #8000): [Syntax.WrongContentBlock]
-- Unexpected declaration
