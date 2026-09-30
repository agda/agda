-- Andreas, 2016-07-29, issue #717
-- reported by LarryTheLiquid on 2012-10-28

data Foo (A : Set) : Set where
  foo : Foo A

data Bar : Set where
  bar baz : Foo {!Bar!} → Bar  -- previously, this IP got duplicated internally

fun : (x : Bar) → Foo Bar
fun (bar y) = {!y!} -- WAS: goal is "Set" (incorrect, should be "Foo Bar")
fun (baz z) = {!z!} -- goal is "Foo Bar" (correct)

-- Works now, after fix for #1720!
