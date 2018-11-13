.. raw:: html
****************
RsTHighlightCode
****************

..
Kenjiro:

    You're already dead!

.. raw:: html
   <a id="98" class="Keyword">module</a> <a id="105" href="RsTHighlightCode.html" class="Module">RsTHighlightCode</a> <a id="122" class="Keyword">where</a>

Shirou Emiya:

    People die when they're killed.

.. raw:: html
   <a id="187" class="Keyword">data</a> <a id="Bool"></a><a id="192" href="RsTHighlightCode.html#192" class="Datatype">Bool</a> <a id="197" class="Symbol">:</a> <a id="199" class="PrimitiveType">Set</a> <a id="203" class="Keyword">where</a>
     <a id="Bool.true"></a><a id="214" href="RsTHighlightCode.html#214" class="InductiveConstructor">true</a> <a id="Bool.false"></a><a id="219" href="RsTHighlightCode.html#219" class="InductiveConstructor">false</a> <a id="225" class="Symbol">:</a> <a id="227" href="RsTHighlightCode.html#192" class="Datatype">Bool</a>

Keine:

    I've been waiting for you.

    Challenging me on the night of a full moon...
    You sure have guts.

.. raw:: html
   <a id="354" class="Keyword">record</a> <a id="Colist"></a><a id="361" href="RsTHighlightCode.html#361" class="Record">Colist</a> <a id="368" class="Symbol">(</a><a id="369" href="RsTHighlightCode.html#369" class="Bound">A</a> <a id="371" class="Symbol">:</a> <a id="373" class="PrimitiveType">Set</a><a id="376" class="Symbol">)</a> <a id="378" class="Symbol">:</a> <a id="380" class="PrimitiveType">Set</a> <a id="384" class="Keyword">where</a>
     <a id="395" class="Keyword">coinductive</a>
     <a id="412" class="Keyword">constructor</a> <a id="Colist._::_"></a><a id="424" href="RsTHighlightCode.html#424" class="CoinductiveConstructor Operator">_::_</a>
     <a id="434" class="Keyword">field</a>
       <a id="Colist.cohead"></a><a id="447" href="RsTHighlightCode.html#447" class="Field">cohead</a> <a id="454" class="Symbol">:</a> <a id="456" href="RsTHighlightCode.html#369" class="Bound">A</a>
       <a id="Colist.cotail"></a><a id="465" href="RsTHighlightCode.html#465" class="Field">cotail</a> <a id="472" class="Symbol">:</a> <a id="474" href="RsTHighlightCode.html#361" class="Record">Colist</a> <a id="481" href="RsTHighlightCode.html#369" class="Bound">A</a>

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
   <a id="731" class="Keyword">open</a> <a id="736" href="RsTHighlightCode.html#361" class="Module">Colist</a>

   <a id="747" class="Keyword">postulate</a>
     <a id="SomeSet"></a><a id="762" href="RsTHighlightCode.html#762" class="Postulate">SomeSet</a> <a id="770" class="Symbol">:</a> <a id="772" class="PrimitiveType">Set</a>
     <a id="SomeVal"></a><a id="781" href="RsTHighlightCode.html#781" class="Postulate">SomeVal</a> <a id="789" class="Symbol">:</a> <a id="791" href="RsTHighlightCode.html#762" class="Postulate">SomeSet</a>

Mokou:

    Even Night Sparrows are drowned in the silence of the forest...
    I wasn't expecting to meet any humans here.

.. raw:: html
   <a id="931" class="Symbol">{-#</a> <a id="935" class="Keyword">NON_TERMINATING</a> <a id="951" class="Symbol">#-}</a>
   <a id="non-terminating-code-blocks"></a><a id="958" href="RsTHighlightCode.html#958" class="Function">non-terminating-code-blocks</a> <a id="986" class="Symbol">:</a> <a id="988" href="RsTHighlightCode.html#361" class="Record">Colist</a> <a id="995" href="RsTHighlightCode.html#762" class="Postulate">SomeSet</a>
   <a id="1006" href="RsTHighlightCode.html#958" class="Function">non-terminating-code-blocks</a> <a id="1034" class="Symbol">=</a>
       <a id="1043" href="RsTHighlightCode.html#781" class="Postulate">SomeVal</a> <a id="1051" href="RsTHighlightCode.html#424" class="CoinductiveConstructor Operator">::</a> <a id="1054" href="RsTHighlightCode.html#958" class="Function">non-terminating-code-blocks</a>

Marisa:

    Who are you?

.. raw:: html
   <a id="1116" class="Keyword">open</a> <a id="1121" class="Keyword">import</a> <a id="1128" href="Agda.Primitive.html" class="Module">Agda.Primitive</a>
   <a id="1146" class="Keyword">variable</a> <a id="1155" href="RsTHighlightCode.html#1155" class="Bound">i</a> <a id="1157" class="Symbol">:</a> <a id="1159" href="Agda.Primitive.html#408" class="Postulate">Level</a>

Alice:

    Marisa, this girl...

.. raw:: html
   <a id="copattern-definitions"></a><a id="1206" href="RsTHighlightCode.html#1206" class="Function">copattern-definitions</a> <a id="1228" class="Symbol">:</a> <a id="1230" href="RsTHighlightCode.html#361" class="Record">Colist</a> <a id="1237" href="RsTHighlightCode.html#762" class="Postulate">SomeSet</a>
   <a id="1248" href="RsTHighlightCode.html#447" class="Field">cohead</a> <a id="1255" href="RsTHighlightCode.html#1206" class="Function">copattern-definitions</a> <a id="1277" class="Symbol">=</a> <a id="1279" href="RsTHighlightCode.html#781" class="Postulate">SomeVal</a>
   <a id="1290" href="RsTHighlightCode.html#465" class="Field">cotail</a> <a id="1297" href="RsTHighlightCode.html#1206" class="Function">copattern-definitions</a> <a id="1319" class="Symbol">=</a> <a id="1321" href="RsTHighlightCode.html#1206" class="Function">copattern-definitions</a>

Mokou:

    I'm a human who's lived here for a long time...
    Don't worry, I'm not interested in eating you.

.. raw:: html
   <a id="1462" class="Keyword">import</a> <a id="1469" href="Agda.Builtin.List.html" class="Module">Agda.Builtin.List</a> <a id="1487" class="Symbol">as</a> <a id="1490" class="Module">List</a>
   <a id="1498" class="Keyword">open</a> <a id="1503" href="Agda.Builtin.List.html" class="Module">List</a>
   <a id="1511" class="Keyword">open</a> <a id="1516" class="Keyword">import</a> <a id="1523" href="Agda.Builtin.Nat.html" class="Module">Agda.Builtin.Nat</a>
     <a id="1545" class="Keyword">renaming</a> <a id="1554" class="Symbol">(</a><a id="1555" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1560" class="Symbol">to</a> <a id="1563" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">O</a><a id="1564" class="Symbol">;</a> <a id="1566" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1570" class="Symbol">to</a> <a id="1573" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">S</a><a id="1574" class="Symbol">)</a>

Marisa:

    Human? Doesn't look like one.

.. raw:: html
   <a id="cotake"></a><a id="1627" href="RsTHighlightCode.html#1627" class="Function">cotake</a> <a id="1634" class="Symbol">:</a> <a id="1636" class="Symbol">{</a><a id="1637" href="RsTHighlightCode.html#1637" class="Bound">A</a> <a id="1639" class="Symbol">:</a> <a id="1641" class="PrimitiveType">Set</a><a id="1644" class="Symbol">}</a> <a id="1646" class="Symbol">-&gt;</a> <a id="1649" href="Agda.Builtin.Nat.html#97" class="Datatype">Nat</a> <a id="1653" class="Symbol">-&gt;</a> <a id="1656" href="RsTHighlightCode.html#361" class="Record">Colist</a> <a id="1663" href="RsTHighlightCode.html#1637" class="Bound">A</a> <a id="1665" class="Symbol">-&gt;</a> <a id="1668" href="Agda.Builtin.List.html#80" class="Datatype">List</a> <a id="1673" href="RsTHighlightCode.html#1637" class="Bound">A</a>
   <a id="1678" href="RsTHighlightCode.html#1627" class="Function">cotake</a> <a id="1685" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">O</a> <a id="1687" class="Symbol">_</a> <a id="1689" class="Symbol">=</a> <a id="1691" href="Agda.Builtin.List.html#117" class="InductiveConstructor">[]</a>
   <a id="1697" href="RsTHighlightCode.html#1627" class="Function">cotake</a> <a id="1704" class="Symbol">(</a><a id="1705" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">S</a> <a id="1707" href="RsTHighlightCode.html#1707" class="Bound">n</a><a id="1708" class="Symbol">)</a> <a id="1710" href="RsTHighlightCode.html#1710" class="Bound">as</a> <a id="1713" class="Symbol">=</a> <a id="1715" href="RsTHighlightCode.html#447" class="Field">cohead</a> <a id="1722" href="RsTHighlightCode.html#1710" class="Bound">as</a> <a id="1725" href="Agda.Builtin.List.html#132" class="InductiveConstructor Operator">∷</a> <a id="1727" href="RsTHighlightCode.html#1627" class="Function">cotake</a> <a id="1734" href="RsTHighlightCode.html#1707" class="Bound">n</a> <a id="1736" class="Symbol">(</a><a id="1737" href="RsTHighlightCode.html#465" class="Field">cotail</a> <a id="1744" href="RsTHighlightCode.html#1710" class="Bound">as</a><a id="1746" class="Symbol">)</a>

Alice:

    Marisa, she's definitely human... but be careful.
