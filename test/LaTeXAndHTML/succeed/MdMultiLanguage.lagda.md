<!--
```
module MdMultiLanguage where
```
-->

  ```haskell
a :: Bool
a = True
```

     ```
data Bool : Set where
    true : Bool
    false : Bool
    aa : {- ``` -} Bool

a : Bool
a = true

```

This is also parsed:

```agda
  module MdQuotedDelim where

        data Bool’ : Set where
            true : Bool’
            false : Bool’
            aa : {- ``` -} Bool’

        a’ : Bool’
        a’ = aa
  ```

* This one is not:

    a : Set
    a = false


* But this one is:

  ```
b : Bool
b = false
 ```
