-- In a module instantiation 'module A = e', 'e' should have the form 'm e1 ..
-- en' where 'm' is a module name.
module NotAModuleExpr where

module Bad = \x -> x

