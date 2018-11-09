## MdHighlightCodeAuto

Wrrryyyyyy!!!

```agda
module MdHighlightCodeAuto where
```

### Scenario A: Blogpost

0. Alice wants to write a blogpost with Agda code. She writes the blog post as a `my-blog-post.lagda.md` file. (1) She wants Agda to typecheck and highlight the Agda code as HTML, and she will then process the markdown into HTML using some other tool (f.ex. pandoc, a static site generator, or a JavaScript slide framework).
0. Case 1, and also in the blog post she uses other modules, whose code she wants to publish together with her blog post as HTML documents. Some of these other modules are .agda files. As for these modules, she wants to render them into a full HTML document.
0. Case 2., and also some of the additional modules are `.lagda.md` files. She wants Agda to output highlighted `.md` files for these modules which she can then process using some other tool.

```agda
data Bool : Set where true false : Bool
youAreAlreadyDead = true
```

