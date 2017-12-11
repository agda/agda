-- Andreas, 2015-07-07 continuation of issue 665

-- Jesper, 2015-12-18 some of these don't work anymore with the new unifier,
-- but a few others that weren't accepted are now.

{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.with.strip:10 #-}
-- {-# OPTIONS -v tc.with.strip:60 -v tc.lhs:20 -v tc.lhs.unify:20 #-}

postulate
  C : Set
  anything : C

record I : Set where
  constructor c
  field
    {f} : C

data Wrap : (i : I) → Set where
  wrap : ∀ {i} → Wrap i

-- Test 0: first argument not given

test0 : ∀ {j} → Wrap j → C
test0 wrap with anything
test0 wrap | z = z

test0a : ∀ {j} → Wrap j → C
test0a (wrap {c {x}}) with anything
test0a  wrap | z = z

test0b : ∀ {j} → Wrap j → C
test0b (wrap {c {_}}) with anything
test0b wrap | z = z

test0c : ∀ {j} → Wrap j → C
test0c (wrap {c}) with anything
test0c wrap | z = z

test0d : ∀ {j} → Wrap j → C
test0d (wrap {c {._}}) with anything
test0d  wrap | z = z

test0e : ∀ {j} → Wrap j → C
test0e (wrap .{c}) with anything
test0e  wrap | z = z

test0f : ∀ {j} → Wrap j → C
test0f (wrap .{c {_}}) with anything
test0f  wrap | z = z

test00 : ∀ {j} → Wrap j → C
test00 wrap with anything
test00 {.c} wrap | z = z

test00a : ∀ {j} → Wrap j → C
test00a (wrap {c {x}}) with anything
test00a {.c} wrap | z = z

test00b : ∀ {j} → Wrap j → C
test00b (wrap {c {_}}) with anything
test00b {.c} wrap | z = z

test00c : ∀ {j} → Wrap j → C
test00c (wrap {c}) with anything
test00c {.c} wrap | z = z

test00d : ∀ {j} → Wrap j → C
test00d (wrap {c {._}}) with anything
test00d {.c} wrap | z = z

test00e : ∀ {j} → Wrap j → C
test00e (wrap .{c}) with anything
test00e {.c} wrap | z = z

test00f : ∀ {j} → Wrap j → C
test00f (wrap .{c {_}}) with anything
test00f {.c} wrap | z = z

test000 : ∀ {j} → Wrap j → C
test000 wrap with anything
test000 .{c {_}} wrap | z = z

test000a : ∀ {j} → Wrap j → C
test000a (wrap {c {x}}) with anything
test000a .{c {_}} wrap | z = z

test000b : ∀ {j} → Wrap j → C
test000b (wrap {c {_}}) with anything
test000b .{c {_}} wrap | z = z

test000c : ∀ {j} → Wrap j → C
test000c (wrap {c}) with anything
test000c .{c {_}} wrap | z = z

test000d : ∀ {j} → Wrap j → C
test000d (wrap {c {._}}) with anything
test000d .{c {_}} wrap | z = z

test000e : ∀ {j} → Wrap j → C
test000e (wrap .{c}) with anything
test000e .{c {_}} wrap | z = z

test000f : ∀ {j} → Wrap j → C
test000f (wrap .{c {_}}) with anything
test000f .{c {_}} wrap | z = z

-- Test 1: first argument is dot pattern

test1a : ∀ {j} → Wrap j → C
test1a .{c} (wrap {c {x}}) with anything
test1a .{c} wrap | z = z

test1b : ∀ {j} → Wrap j → C
test1b .{c} (wrap {c {_}}) with anything
test1b .{c} wrap | z = z

test1c : ∀ {j} → Wrap j → C
test1c .{c} (wrap {c}) with anything
test1c .{c} wrap | z = z

test11a : ∀ {j} → Wrap j → C
test11a .{c} (wrap {c {x}}) with anything
test11a wrap | z = z

test11b : ∀ {j} → Wrap j → C
test11b .{c} (wrap {c {_}}) with anything
test11b wrap | z = z

test11c : ∀ {j} → Wrap j → C
test11c .{c} (wrap {c}) with anything
test11c wrap | z = z

test111a : ∀ {j} → Wrap j → C
test111a (wrap {c {x}}) with anything
test111a .{c} wrap | z = z

test111b : ∀ {j} → Wrap j → C
test111b (wrap {c {_}}) with anything
test111b .{c} wrap | z = z

test111c : ∀ {j} → Wrap j → C
test111c (wrap {c}) with anything
test111c .{c} wrap | z = z

-- Test 2: First argument is record pattern

test2a : ∀ {j} → Wrap j → C
test2a {c} wrap with anything
test2a {c} wrap | z = z

test2b : ∀ {j} → Wrap j → C
test2b {c} wrap with anything
test2b wrap | z = z

test2c : ∀ {j} → Wrap j → C
test2c {c} (wrap {c}) with anything
test2c {c} wrap | z = z

test2d : ∀ {j} → Wrap j → C
test2d {c} (wrap {c}) with anything
test2d wrap | z = z

test2e : ∀ {j} → Wrap j → C
test2e {c} (wrap {c {._}}) with anything
test2e {c} wrap | z = z

test2f : ∀ {j} → Wrap j → C
test2f {c} (wrap {c {._}}) with anything
test2f wrap | z = z

test2g : ∀ {j} → Wrap j → C
test2g {c} (wrap {c {x}}) with anything
test2g {c} wrap | z = z

test2h : ∀ {j} → Wrap j → C
test2h {c} (wrap {c {x}}) with anything
test2h wrap | z = z

test2i : ∀ {j} → Wrap j → C
test2i {c} (wrap {c {_}}) with anything
test2i {c} wrap | z = z

test2j : ∀ {j} → Wrap j → C
test2j {c} (wrap {c {_}}) with anything
test2j wrap | z = z

-- Test 3: First argument is record of dot pattern, second is record pattern

test3a : ∀ {j} → Wrap j → C
test3a {c {._}} wrap with anything
test3a {c {._}} wrap | z = z

test3b : ∀ {j} → Wrap j → C
test3b {c {._}} wrap with anything
test3b wrap | z = z

test3c : ∀ {j} → Wrap j → C
test3c {c {._}} (wrap {c}) with anything
test3c {c {._}} wrap | z = z

test3d : ∀ {j} → Wrap j → C
test3d {c {._}} (wrap {c}) with anything
test3d wrap | z = z

test3e : ∀ {j} → Wrap j → C
test3e {c {._}} (wrap {c {._}}) with anything
test3e {c {._}} wrap | z = z

test3f : ∀ {j} → Wrap j → C
test3f {c {._}} (wrap {c {._}}) with anything
test3f wrap | z = z

test3g : ∀ {j} → Wrap j → C
test3g {c {_}} (wrap {c {x}}) with anything
test3g {c {_}} wrap | z = z

test3h : ∀ {j} → Wrap j → C
test3h {c {_}} (wrap {c {x}}) with anything
test3h wrap | z = z

test3i : ∀ {j} → Wrap j → C
test3i {c {_}} (wrap {c {_}}) with anything
test3i {c {_}} wrap | z = z

test3j : ∀ {j} → Wrap j → C
test3j {c {_}} (wrap {c {_}}) with anything
test3j wrap | z = z
