<!-- Test for issue #7971: https://github.com/agda/agda/issues/7971
     Date: 2025-12-01

     This test demonstrates that when --literate-md-only-agda-blocks is enabled,
     only code blocks explicitly marked with ```agda are treated as Agda code.
     Unmarked code blocks (```) are treated as verbatim text and not type-checked.

     Note: The option is passed via .flags file because it affects parsing,
     which happens before pragma options are applied.

     Expected behavior: The module should type-check successfully, ignoring the
     verbatim blocks that contain invalid Agda syntax.
-->

# Literate Markdown with Only Agda Blocks

This is a test file demonstrating the `--literate-md-only-agda-blocks` option.

```agda
module Issue7971LiterateMdOnlyAgdaBlocks where
```

## Valid Agda Code

Here is some valid Agda code in a marked block:

```agda
data Bool : Set where
  true  : Bool
  false : Bool
```

## Verbatim Blocks (Not Type-Checked)

The following unmarked code block contains text that is NOT valid Agda code.
With `--literate-md-only-agda-blocks`, this is treated as verbatim text:

```
This is not valid Agda code!
function hello() { return "world"; }
The parser will skip this block entirely.
```

Here's another example with a programming language tag:

```javascript
// JavaScript code - not type-checked
const x = 42;
console.log(x);
```

And another unmarked block:

```
! @ # $ % ^ & * ( ) { } [ ] | \ ~ \`
invalid :: syntax -> everywhere
```

## More Valid Agda Code

Back to valid Agda in a marked block:

```agda
not : Bool → Bool
not true  = false
not false = true
```

## Final Verification

This works correctly:

```agda
_ : Bool
_ = not true
```
