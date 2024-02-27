.. raw:: html
********************
RsTHighlightCodeAuto
********************

..

.. raw:: html
   <a id="75" class="Symbol">{-#</a> <a id="79" class="Keyword">OPTIONS</a> <a id="87" class="Pragma">--sized-types</a> <a id="101" class="Symbol">#-}</a>
   <a id="108" class="Keyword">module</a> <a id="115" href="RsTHighlightCodeAuto.html" class="Module">RsTHighlightCodeAuto</a> <a id="136" class="Keyword">where</a>

Mokou:
    So, what are you doing out this late?

.. raw:: html
   <a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="Agda.Builtin.Size.html" class="Module">Agda.Builtin.Size</a>
   <a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>

Marisa:
    Harvesting bamboo shoots.
.. raw:: html
   <a id="304" class="Keyword">variable</a>
     <a id="318" href="RsTHighlightCodeAuto.html#318" class="Generalizable">i</a> <a id="320" class="Symbol">:</a> <a id="322" href="Agda.Builtin.Size.html#213" class="Postulate">Size</a>

   <a id="331" class="Comment">-- Alice:</a>
   <a id="344" class="Comment">--    A trial of guts.</a>

     <a id="373" href="RsTHighlightCodeAuto.html#373" class="Generalizable">ℓ</a> <a id="375" class="Symbol">:</a> <a id="377" href="Agda.Primitive.html#742" class="Postulate">Level</a>

   <a id="387" class="Comment">-- Mokou:</a>
   <a id="400" class="Comment">--    Uh, which one is it?</a>

Comment tests ↑

.. raw:: html
     <a id="453" href="RsTHighlightCodeAuto.html#453" class="Generalizable">A</a> <a id="455" class="Symbol">:</a> <a id="457" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="461" href="RsTHighlightCodeAuto.html#373" class="Generalizable">ℓ</a>
   -- Marisa:
   --   That should've been obvious...

.. raw:: html
   <a id="523" class="Keyword">record</a> <a id="Thunk"></a><a id="530" href="RsTHighlightCodeAuto.html#530" class="Record">Thunk</a> <a id="536" class="Symbol">{</a><a id="537" href="RsTHighlightCodeAuto.html#537" class="Bound">ℓ</a><a id="538" class="Symbol">}</a> <a id="540" class="Symbol">(</a><a id="541" href="RsTHighlightCodeAuto.html#541" class="Bound">F</a> <a id="543" class="Symbol">:</a> <a id="545" href="Agda.Builtin.Size.html#213" class="Postulate">Size</a> <a id="550" class="Symbol">→</a> <a id="552" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="556" href="RsTHighlightCodeAuto.html#537" class="Bound">ℓ</a><a id="557" class="Symbol">)</a> <a id="559" class="Symbol">(</a><a id="560" href="RsTHighlightCodeAuto.html#560" class="Bound">i</a> <a id="562" class="Symbol">:</a> <a id="564" href="Agda.Builtin.Size.html#213" class="Postulate">Size</a><a id="568" class="Symbol">)</a> <a id="570" class="Symbol">:</a> <a id="572" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="576" href="RsTHighlightCodeAuto.html#537" class="Bound">ℓ</a> <a id="578" class="Keyword">where</a>
     <a id="589" class="Keyword">coinductive</a>

Mokou:
    The medicine? You mean the Hourai Elixir?
    I consumed it a long time ago.
    Thanks to the elixir, I am immortal even now.
    Kaguya still tries to kill me.
    But it's impossible.
    This meaningless conflict has dragged on for over a thousand years.

.. raw:: html
     <a id="881" class="Keyword">field</a> <a id="Thunk.force"></a><a id="887" href="RsTHighlightCodeAuto.html#887" class="Field">force</a> <a id="893" class="Symbol">:</a> <a id="895" class="Symbol">{</a><a id="896" href="RsTHighlightCodeAuto.html#896" class="Bound">j</a> <a id="898" class="Symbol">:</a> <a id="900" href="Agda.Builtin.Size.html#247" class="Postulate Operator">Size&lt;</a> <a id="906" href="RsTHighlightCodeAuto.html#560" class="Bound">i</a><a id="907" class="Symbol">}</a> <a id="909" class="Symbol">→</a> <a id="911" href="RsTHighlightCodeAuto.html#541" class="Bound">F</a> <a id="913" href="RsTHighlightCodeAuto.html#896" class="Bound">j</a>
   open Thunk public

Marisa:
    I get it. I understand now...
    So, you're playing the role of the ghost in the haunted house.
    I was suspicious when I first heard about this "trial of guts" thing from Kaguya.
    She must have thought that I, who defeated her, might be able to crush you.

.. raw:: html
   <a id="1219" class="Keyword">data</a> <a id="Conat"></a><a id="1224" href="RsTHighlightCodeAuto.html#1224" class="Datatype">Conat</a> <a id="1230" class="Symbol">(</a><a id="1231" href="RsTHighlightCodeAuto.html#1231" class="Bound">i</a> <a id="1233" class="Symbol">:</a> <a id="1235" href="Agda.Builtin.Size.html#213" class="Postulate">Size</a><a id="1239" class="Symbol">)</a> <a id="1241" class="Symbol">:</a> <a id="1243" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1247" class="Keyword">where</a>
     <a id="Conat.zero"></a><a id="1258" href="RsTHighlightCodeAuto.html#1258" class="InductiveConstructor">zero</a> <a id="1263" class="Symbol">:</a> <a id="1265" href="RsTHighlightCodeAuto.html#1224" class="Datatype">Conat</a> <a id="1271" href="RsTHighlightCodeAuto.html#1231" class="Bound">i</a>
     <a id="Conat.suc"></a><a id="1278" href="RsTHighlightCodeAuto.html#1278" class="InductiveConstructor">suc</a> <a id="1282" class="Symbol">:</a> <a id="1284" href="RsTHighlightCodeAuto.html#530" class="Record">Thunk</a> <a id="1290" href="RsTHighlightCodeAuto.html#1224" class="Datatype">Conat</a> <a id="1296" href="RsTHighlightCodeAuto.html#1231" class="Bound">i</a> <a id="1298" class="Symbol">→</a> <a id="1300" href="RsTHighlightCodeAuto.html#1224" class="Datatype">Conat</a> <a id="1306" href="RsTHighlightCodeAuto.html#1231" class="Bound">i</a>

Alice:
    Wait, aren't you stealing all the credit for yourself?
    Besides, crushing humans is a youkai's role.
    The human before us is obviously mine to crush.

.. raw:: html
   <a id="infinity"></a><a id="1483" href="RsTHighlightCodeAuto.html#1483" class="Function">infinity</a> <a id="1492" class="Symbol">:</a> <a id="1494" href="RsTHighlightCodeAuto.html#1224" class="Datatype">Conat</a> <a id="1500" href="RsTHighlightCodeAuto.html#318" class="Generalizable">i</a>
   <a id="1505" href="RsTHighlightCodeAuto.html#1483" class="Function">infinity</a> <a id="1514" class="Symbol">=</a> <a id="1516" href="RsTHighlightCodeAuto.html#1278" class="InductiveConstructor">suc</a> <a id="1520" class="Symbol">λ</a> <a id="1522" class="Keyword">where</a> <a id="1528" class="Symbol">.</a><a id="1529" href="RsTHighlightCodeAuto.html#887" class="Field">Thunk.force</a> <a id="1541" class="Symbol">→</a> <a id="1543" href="RsTHighlightCodeAuto.html#1483" class="Function">infinity</a>

Mokou:
    What, Kaguya was defeated?
    By the two of you who stand before me?
    That's quite surprising. That troublesome Lunarian was defeated by such a team...
    It's been a long time since I've confronted such tough assassins.
    Or maybe the only thing that's tough about them is their guts?

.. raw:: html
   <a id="1864" class="Keyword">open</a> <a id="1869" class="Keyword">import</a> <a id="1876" href="Agda.Builtin.Nat.html" class="Module">Agda.Builtin.Nat</a>

   <a id="fromℕ"></a><a id="1897" href="RsTHighlightCodeAuto.html#1897" class="Function">fromℕ</a> <a id="1903" class="Symbol">:</a> <a id="1905" href="Agda.Builtin.Nat.html#228" class="Datatype">Nat</a> <a id="1909" class="Symbol">→</a> <a id="1911" href="RsTHighlightCodeAuto.html#1224" class="Datatype">Conat</a> <a id="1917" href="Agda.Builtin.Size.html#315" class="Postulate">∞</a>
   <a id="1922" href="RsTHighlightCodeAuto.html#1897" class="Function">fromℕ</a> <a id="1928" href="Agda.Builtin.Nat.html#246" class="InductiveConstructor">zero</a>    <a id="1936" class="Symbol">=</a> <a id="1938" href="RsTHighlightCodeAuto.html#1258" class="InductiveConstructor">zero</a>
   <a id="1946" href="RsTHighlightCodeAuto.html#1897" class="Function">fromℕ</a> <a id="1952" class="Symbol">(</a><a id="1953" href="Agda.Builtin.Nat.html#259" class="InductiveConstructor">suc</a> <a id="1957" href="RsTHighlightCodeAuto.html#1957" class="Bound">n</a><a id="1958" class="Symbol">)</a> <a id="1960" class="Symbol">=</a> <a id="1962" href="RsTHighlightCodeAuto.html#1278" class="InductiveConstructor">suc</a> <a id="1966" class="Symbol">λ</a> <a id="1968" class="Keyword">where</a> <a id="1974" class="Symbol">.</a><a id="1975" href="RsTHighlightCodeAuto.html#887" class="Field">Thunk.force</a> <a id="1987" class="Symbol">→</a> <a id="1989" href="RsTHighlightCodeAuto.html#1897" class="Function">fromℕ</a> <a id="1995" href="RsTHighlightCodeAuto.html#1957" class="Bound">n</a>

Alice:
    It's too bad about that Hourai Elixir.
    I wanted it for my collection.

.. raw:: html
   <a id="2090" class="Comment">-- Why can&#39;t we have goals in literate Agda mode?</a>
