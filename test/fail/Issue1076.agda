module Issue1076 where

{-# OPTIONS --no-coverage-check #-}

-- WAS: Parse error

-- NOW:
-- OPTIONS pragma only allowed at beginning of file, before top module
-- declaration
-- when checking the pragma OPTIONS --no-coverage-check
