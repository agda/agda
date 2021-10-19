## MdHighlightCodeAuto

Wrrryyyyyy!!!

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="MdHighlightCodeAuto.html" class="Module">MdHighlightCodeAuto</a> <a id="75" class="Keyword">where</a>
</pre>
### Scenario A: Blogpost

0. Alice wants to write a blogpost with Agda code. She writes the blog post as a `my-blog-post.lagda.md` file. (1) She wants Agda to typecheck and highlight the Agda code as HTML, and she will then process the markdown into HTML using some other tool (f.ex. pandoc, a static site generator, or a JavaScript slide framework).
0. Case 1, and also in the blog post she uses other modules, whose code she wants to publish together with her blog post as HTML documents. Some of these other modules are .agda files. As for these modules, she wants to render them into a full HTML document.
0. Case 2., and also some of the additional modules are `.lagda.md` files. She wants Agda to output highlighted `.md` files for these modules which she can then process using some other tool.

<pre class="Agda"><a id="897" class="Keyword">data</a> <a id="Bool"></a><a id="902" href="MdHighlightCodeAuto.html#902" class="Datatype">Bool</a> <a id="907" class="Symbol">:</a> <a id="909" href="Agda.Primitive.html#311" class="Primitive">Set</a> <a id="913" class="Keyword">where</a> <a id="Bool.true"></a><a id="919" href="MdHighlightCodeAuto.html#919" class="InductiveConstructor">true</a> <a id="Bool.false"></a><a id="924" href="MdHighlightCodeAuto.html#924" class="InductiveConstructor">false</a> <a id="930" class="Symbol">:</a> <a id="932" href="MdHighlightCodeAuto.html#902" class="Datatype">Bool</a>
<a id="youAreAlreadyDead"></a><a id="937" href="MdHighlightCodeAuto.html#937" class="Function">youAreAlreadyDead</a> <a id="955" class="Symbol">=</a> <a id="957" href="MdHighlightCodeAuto.html#919" class="InductiveConstructor">true</a>
</pre>
