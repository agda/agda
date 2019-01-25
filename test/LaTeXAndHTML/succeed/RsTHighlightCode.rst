.. raw:: html
****************
RsTHighlightCode
****************

..
Kenjiro:

    You're already dead!

.. raw:: html
   <a id="98" class="Symbol">{-#</a> <a id="102" class="Keyword">OPTIONS</a> <a id="110" class="Pragma">--guardedness</a> <a id="124" class="Symbol">#-}</a>

   <a id="132" class="Keyword">module</a> <a id="139" href="RsTHighlightCode.html" class="Module">RsTHighlightCode</a> <a id="156" class="Keyword">where</a>

Shirou Emiya:

    People die when they're killed.

.. raw:: html
   <a id="221" class="Keyword">data</a> <a id="Bool"></a><a id="226" href="RsTHighlightCode.html#226" class="Datatype">Bool</a> <a id="231" class="Symbol">:</a> <a id="233" class="PrimitiveType">Set</a> <a id="237" class="Keyword">where</a>
     <a id="Bool.true"></a><a id="248" href="RsTHighlightCode.html#248" class="InductiveConstructor">true</a> <a id="Bool.false"></a><a id="253" href="RsTHighlightCode.html#253" class="InductiveConstructor">false</a> <a id="259" class="Symbol">:</a> <a id="261" href="RsTHighlightCode.html#226" class="Datatype">Bool</a>

Keine:

    I've been waiting for you.

    Challenging me on the night of a full moon...
    You sure have guts.

.. raw:: html
   <a id="388" class="Keyword">record</a> <a id="Colist"></a><a id="395" href="RsTHighlightCode.html#395" class="Record">Colist</a> <a id="402" class="Symbol">(</a><a id="403" href="RsTHighlightCode.html#403" class="Bound">A</a> <a id="405" class="Symbol">:</a> <a id="407" class="PrimitiveType">Set</a><a id="410" class="Symbol">)</a> <a id="412" class="Symbol">:</a> <a id="414" class="PrimitiveType">Set</a> <a id="418" class="Keyword">where</a>
     <a id="429" class="Keyword">coinductive</a>
     <a id="446" class="Keyword">constructor</a> <a id="Colist._::_"></a><a id="458" href="RsTHighlightCode.html#458" class="CoinductiveConstructor Operator">_::_</a>
     <a id="468" class="Keyword">field</a>
       <a id="Colist.cohead"></a><a id="481" href="RsTHighlightCode.html#481" class="Field">cohead</a> <a id="488" class="Symbol">:</a> <a id="490" href="RsTHighlightCode.html#403" class="Bound">A</a>
       <a id="Colist.cotail"></a><a id="499" href="RsTHighlightCode.html#499" class="Field">cotail</a> <a id="506" class="Symbol">:</a> <a id="508" href="RsTHighlightCode.html#395" class="Record">Colist</a> <a id="515" href="RsTHighlightCode.html#403" class="Bound">A</a>

Marisa:

    Good thing we're on a trial of guts anyway.

.. code-block:: agda

   record R : Set where
     field x : X

   module M where x = ...

   r : R
   r = record { M; z = ... }

Keine:

    You may not lay a single finger on her!

.. raw:: html
   <a id="765" class="Keyword">open</a> <a id="770" href="RsTHighlightCode.html#395" class="Module">Colist</a>

   <a id="781" class="Keyword">postulate</a>
     <a id="SomeSet"></a><a id="796" href="RsTHighlightCode.html#796" class="Postulate">SomeSet</a> <a id="804" class="Symbol">:</a> <a id="806" class="PrimitiveType">Set</a>
     <a id="SomeVal"></a><a id="815" href="RsTHighlightCode.html#815" class="Postulate">SomeVal</a> <a id="823" class="Symbol">:</a> <a id="825" href="RsTHighlightCode.html#796" class="Postulate">SomeSet</a>

Mokou:

    Even Night Sparrows are drowned in the silence of the forest...
    I wasn't expecting to meet any humans here.

.. raw:: html
   <a id="965" class="Symbol">{-#</a> <a id="969" class="Keyword">NON_TERMINATING</a> <a id="985" class="Symbol">#-}</a>
   <a id="non-terminating-code-blocks"></a><a id="992" href="RsTHighlightCode.html#992" class="Function">non-terminating-code-blocks</a> <a id="1020" class="Symbol">:</a> <a id="1022" href="RsTHighlightCode.html#395" class="Record">Colist</a> <a id="1029" href="RsTHighlightCode.html#796" class="Postulate">SomeSet</a>
   <a id="1040" href="RsTHighlightCode.html#992" class="Function">non-terminating-code-blocks</a> <a id="1068" class="Symbol">=</a>
       <a id="1077" href="RsTHighlightCode.html#815" class="Postulate">SomeVal</a> <a id="1085" href="RsTHighlightCode.html#458" class="CoinductiveConstructor Operator">::</a> <a id="1088" href="RsTHighlightCode.html#992" class="Function">non-terminating-code-blocks</a>

Marisa:

    Who are you?

.. raw:: html
   <a id="1150" class="Keyword">open</a> <a id="1155" class="Keyword">import</a> <a id="1162" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
   <a id="1180" class="Keyword">variable</a> <a id="1189" href="RsTHighlightCode.html#1189" class="Bound">i</a> <a id="1191" class="Symbol">:</a> <a id="1193" href="Agda.Primitive.html#408" class="Postulate">Level</a>

Alice:

    Marisa, this girl...

.. raw:: html
   <a id="copattern-definitions"></a><a id="1240" href="RsTHighlightCode.html#1240" class="Function">copattern-definitions</a> <a id="1262" class="Symbol">:</a> <a id="1264" href="RsTHighlightCode.html#395" class="Record">Colist</a> <a id="1271" href="RsTHighlightCode.html#796" class="Postulate">SomeSet</a>
   <a id="1282" href="RsTHighlightCode.html#481" class="Field">cohead</a> <a id="1289" href="RsTHighlightCode.html#1240" class="Function">copattern-definitions</a> <a id="1311" class="Symbol">=</a> <a id="1313" href="RsTHighlightCode.html#815" class="Postulate">SomeVal</a>
   <a id="1324" href="RsTHighlightCode.html#499" class="Field">cotail</a> <a id="1331" href="RsTHighlightCode.html#1240" class="Function">copattern-definitions</a> <a id="1353" class="Symbol">=</a> <a id="1355" href="RsTHighlightCode.html#1240" class="Function">copattern-definitions</a>

Mokou:

    I'm a human who's lived here for a long time...
    Don't worry, I'm not interested in eating you.

.. raw:: html
   <a id="1496" class="Keyword">import</a> <a id="1503" href="Agda.Builtin.List.html" class="Module">Agda.Builtin.List</a> <a id="1521" class="Symbol">as</a> <a id="1524" class="Module">List</a>
   <a id="1532" class="Keyword">open</a> <a id="1537" href="Agda.Builtin.List.html" class="Module">List</a>
   <a id="1545" class="Keyword">open</a> <a id="1550" class="Keyword">import</a> <a id="1557" href="Agda.Builtin.Nat.html" class="Module">Agda.Builtin.Nat</a>
     <a id="1579" class="Keyword">renaming</a> <a id="1588" class="Symbol">(</a><a id="1589" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1594" class="Symbol">to</a> <a id="1597" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">O</a><a id="1598" class="Symbol">;</a> <a id="1600" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1604" class="Symbol">to</a> <a id="1607" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">S</a><a id="1608" class="Symbol">)</a>

Marisa:

    Human? Doesn't look like one.

.. raw:: html
   <a id="cotake"></a><a id="1661" href="RsTHighlightCode.html#1661" class="Function">cotake</a> <a id="1668" class="Symbol">:</a> <a id="1670" class="Symbol">{</a><a id="1671" href="RsTHighlightCode.html#1671" class="Bound">A</a> <a id="1673" class="Symbol">:</a> <a id="1675" class="PrimitiveType">Set</a><a id="1678" class="Symbol">}</a> <a id="1680" class="Symbol">-&gt;</a> <a id="1683" href="Agda.Builtin.Nat.html#165" class="Datatype">Nat</a> <a id="1687" class="Symbol">-&gt;</a> <a id="1690" href="RsTHighlightCode.html#395" class="Record">Colist</a> <a id="1697" href="RsTHighlightCode.html#1671" class="Bound">A</a> <a id="1699" class="Symbol">-&gt;</a> <a id="1702" href="Agda.Builtin.List.html#121" class="Datatype">List</a> <a id="1707" href="RsTHighlightCode.html#1671" class="Bound">A</a>
   <a id="1712" href="RsTHighlightCode.html#1661" class="Function">cotake</a> <a id="1719" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">O</a> <a id="1721" class="Symbol">_</a> <a id="1723" class="Symbol">=</a> <a id="1725" href="Agda.Builtin.List.html#158" class="InductiveConstructor">[]</a>
   <a id="1731" href="RsTHighlightCode.html#1661" class="Function">cotake</a> <a id="1738" class="Symbol">(</a><a id="1739" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">S</a> <a id="1741" href="RsTHighlightCode.html#1741" class="Bound">n</a><a id="1742" class="Symbol">)</a> <a id="1744" href="RsTHighlightCode.html#1744" class="Bound">as</a> <a id="1747" class="Symbol">=</a> <a id="1749" href="RsTHighlightCode.html#481" class="Field">cohead</a> <a id="1756" href="RsTHighlightCode.html#1744" class="Bound">as</a> <a id="1759" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">∷</a> <a id="1761" href="RsTHighlightCode.html#1661" class="Function">cotake</a> <a id="1768" href="RsTHighlightCode.html#1741" class="Bound">n</a> <a id="1770" class="Symbol">(</a><a id="1771" href="RsTHighlightCode.html#499" class="Field">cotail</a> <a id="1778" href="RsTHighlightCode.html#1744" class="Bound">as</a><a id="1780" class="Symbol">)</a>

Alice:

    Marisa, she's definitely human... but be careful.
