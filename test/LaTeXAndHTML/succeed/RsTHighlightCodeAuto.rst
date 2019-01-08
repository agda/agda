.. raw:: html
********************
RsTHighlightCodeAuto
********************

..

.. raw:: html
   <a id="75" class="Keyword">module</a> <a id="82" href="RsTHighlightCodeAuto.html" class="Module">RsTHighlightCodeAuto</a> <a id="103" class="Keyword">where</a>

Mokou:
    So, what are you doing out this late?

.. raw:: html
   <a id="166" class="Keyword">open</a> <a id="171" class="Keyword">import</a> <a id="178" href="Agda.Builtin.Size.html" class="Module">Agda.Builtin.Size</a>
   <a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>

Marisa:
    Harvesting bamboo shoots.
.. raw:: html
   <a id="271" class="Keyword">variable</a>
     <a id="285" href="RsTHighlightCodeAuto.html#285" class="Bound">i</a> <a id="287" class="Symbol">:</a> <a id="289" href="Agda.Builtin.Size.html#182" class="Postulate">Size</a>

   <a id="298" class="Comment">-- Alice:</a>
   <a id="311" class="Comment">--    A trial of guts.</a>

     <a id="340" href="RsTHighlightCodeAuto.html#340" class="Bound">ℓ</a> <a id="342" class="Symbol">:</a> <a id="344" href="Agda.Primitive.html#408" class="Postulate">Level</a>

   <a id="354" class="Comment">-- Mokou:</a>
   <a id="367" class="Comment">--    Uh, which one is it?</a>

Comment tests ↑

.. raw:: html
     <a id="420" href="RsTHighlightCodeAuto.html#420" class="Bound">A</a> <a id="422" class="Symbol">:</a> <a id="424" class="PrimitiveType">Set</a> <a id="428" href="RsTHighlightCodeAuto.html#340" class="Bound">ℓ</a>
   -- Marisa:
   --   That should've been obvious...

.. raw:: html
   <a id="490" class="Keyword">record</a> <a id="Thunk"></a><a id="497" href="RsTHighlightCodeAuto.html#497" class="Record">Thunk</a> <a id="503" class="Symbol">{</a><a id="504" href="RsTHighlightCodeAuto.html#504" class="Bound">ℓ</a><a id="505" class="Symbol">}</a> <a id="507" class="Symbol">(</a><a id="508" href="RsTHighlightCodeAuto.html#508" class="Bound">F</a> <a id="510" class="Symbol">:</a> <a id="512" href="Agda.Builtin.Size.html#182" class="Postulate">Size</a> <a id="517" class="Symbol">→</a> <a id="519" class="PrimitiveType">Set</a> <a id="523" href="RsTHighlightCodeAuto.html#504" class="Bound">ℓ</a><a id="524" class="Symbol">)</a> <a id="526" class="Symbol">(</a><a id="527" href="RsTHighlightCodeAuto.html#527" class="Bound">i</a> <a id="529" class="Symbol">:</a> <a id="531" href="Agda.Builtin.Size.html#182" class="Postulate">Size</a><a id="535" class="Symbol">)</a> <a id="537" class="Symbol">:</a> <a id="539" class="PrimitiveType">Set</a> <a id="543" href="RsTHighlightCodeAuto.html#504" class="Bound">ℓ</a> <a id="545" class="Keyword">where</a>
     <a id="556" class="Keyword">coinductive</a>

Mokou:
    The medicine? You mean the Hourai Elixir?
    I consumed it a long time ago.
    Thanks to the elixir, I am immortal even now.
    Kaguya still tries to kill me.
    But it's impossible.
    This meaningless conflict has dragged on for over a thousand years.

.. raw:: html
     <a id="848" class="Keyword">field</a> <a id="Thunk.force"></a><a id="854" href="RsTHighlightCodeAuto.html#854" class="Field">force</a> <a id="860" class="Symbol">:</a> <a id="862" class="Symbol">{</a><a id="863" href="RsTHighlightCodeAuto.html#863" class="Bound">j</a> <a id="865" class="Symbol">:</a> <a id="867" href="Agda.Builtin.Size.html#214" class="Postulate Operator">Size&lt;</a> <a id="873" href="RsTHighlightCodeAuto.html#527" class="Bound">i</a><a id="874" class="Symbol">}</a> <a id="876" class="Symbol">→</a> <a id="878" href="RsTHighlightCodeAuto.html#508" class="Bound">F</a> <a id="880" href="RsTHighlightCodeAuto.html#863" class="Bound">j</a>
   open Thunk public

Marisa:
    I get it. I understand now...
    So, you're playing the role of the ghost in the haunted house.
    I was suspicious when I first heard about this "trial of guts" thing from Kaguya.
    She must have thought that I, who defeated her, might be able to crush you.

.. raw:: html
   <a id="1186" class="Keyword">data</a> <a id="Conat"></a><a id="1191" href="RsTHighlightCodeAuto.html#1191" class="Datatype">Conat</a> <a id="1197" class="Symbol">(</a><a id="1198" href="RsTHighlightCodeAuto.html#1198" class="Bound">i</a> <a id="1200" class="Symbol">:</a> <a id="1202" href="Agda.Builtin.Size.html#182" class="Postulate">Size</a><a id="1206" class="Symbol">)</a> <a id="1208" class="Symbol">:</a> <a id="1210" class="PrimitiveType">Set</a> <a id="1214" class="Keyword">where</a>
     <a id="Conat.zero"></a><a id="1225" href="RsTHighlightCodeAuto.html#1225" class="InductiveConstructor">zero</a> <a id="1230" class="Symbol">:</a> <a id="1232" href="RsTHighlightCodeAuto.html#1191" class="Datatype">Conat</a> <a id="1238" href="RsTHighlightCodeAuto.html#1198" class="Bound">i</a>
     <a id="Conat.suc"></a><a id="1245" href="RsTHighlightCodeAuto.html#1245" class="InductiveConstructor">suc</a> <a id="1249" class="Symbol">:</a> <a id="1251" href="RsTHighlightCodeAuto.html#497" class="Record">Thunk</a> <a id="1257" href="RsTHighlightCodeAuto.html#1191" class="Datatype">Conat</a> <a id="1263" href="RsTHighlightCodeAuto.html#1198" class="Bound">i</a> <a id="1265" class="Symbol">→</a> <a id="1267" href="RsTHighlightCodeAuto.html#1191" class="Datatype">Conat</a> <a id="1273" href="RsTHighlightCodeAuto.html#1198" class="Bound">i</a>

Alice:
    Wait, aren't you stealing all the credit for yourself?
    Besides, crushing humans is a youkai's role.
    The human before us is obviously mine to crush.

.. raw:: html
   <a id="infinity"></a><a id="1450" href="RsTHighlightCodeAuto.html#1450" class="Function">infinity</a> <a id="1459" class="Symbol">:</a> <a id="1461" href="RsTHighlightCodeAuto.html#1191" class="Datatype">Conat</a> <a id="1467" href="RsTHighlightCodeAuto.html#285" class="Bound">i</a>
   <a id="1472" href="RsTHighlightCodeAuto.html#1450" class="Function">infinity</a> <a id="1481" class="Symbol">=</a> <a id="1483" href="RsTHighlightCodeAuto.html#1245" class="InductiveConstructor">suc</a> <a id="1487" class="Symbol">λ</a> <a id="1489" class="Keyword">where</a> <a id="1495" class="Symbol">.</a><a id="1496" href="RsTHighlightCodeAuto.html#854" class="Field">Thunk.force</a> <a id="1508" class="Symbol">→</a> <a id="1510" href="RsTHighlightCodeAuto.html#1450" class="Function">infinity</a>

Mokou:
    What, Kaguya was defeated?
    By the two of you who stand before me?
    That's quite surprising. That troublesome Lunarian was defeated by such a team...
    It's been a long time since I've confronted such tough assassins.
    Or maybe the only thing that's tough about them is their guts?

.. raw:: html
   <a id="1831" class="Keyword">open</a> <a id="1836" class="Keyword">import</a> <a id="1843" href="Agda.Builtin.Nat.html" class="Module">Agda.Builtin.Nat</a>

   <a id="fromℕ"></a><a id="1864" href="RsTHighlightCodeAuto.html#1864" class="Function">fromℕ</a> <a id="1870" class="Symbol">:</a> <a id="1872" href="Agda.Builtin.Nat.html#165" class="Datatype">Nat</a> <a id="1876" class="Symbol">→</a> <a id="1878" href="RsTHighlightCodeAuto.html#1191" class="Datatype">Conat</a> <a id="1884" href="Agda.Builtin.Size.html#278" class="Postulate">∞</a>
   <a id="1889" href="RsTHighlightCodeAuto.html#1864" class="Function">fromℕ</a> <a id="1895" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="1903" class="Symbol">=</a> <a id="1905" href="RsTHighlightCodeAuto.html#1225" class="InductiveConstructor">zero</a>
   <a id="1913" href="RsTHighlightCodeAuto.html#1864" class="Function">fromℕ</a> <a id="1919" class="Symbol">(</a><a id="1920" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1924" href="RsTHighlightCodeAuto.html#1924" class="Bound">n</a><a id="1925" class="Symbol">)</a> <a id="1927" class="Symbol">=</a> <a id="1929" href="RsTHighlightCodeAuto.html#1245" class="InductiveConstructor">suc</a> <a id="1933" class="Symbol">λ</a> <a id="1935" class="Keyword">where</a> <a id="1941" class="Symbol">.</a><a id="1942" href="RsTHighlightCodeAuto.html#854" class="Field">Thunk.force</a> <a id="1954" class="Symbol">→</a> <a id="1956" href="RsTHighlightCodeAuto.html#1864" class="Function">fromℕ</a> <a id="1962" href="RsTHighlightCodeAuto.html#1924" class="Bound">n</a>

Alice:
    It's too bad about that Hourai Elixir.
    I wanted it for my collection.

.. raw:: html
   <a id="2057" class="Comment">-- Why can&#39;t we have goals in literate Agda mode?</a>
