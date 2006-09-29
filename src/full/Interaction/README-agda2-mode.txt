To use emacs mode for Agda2

0. Install haskell-mode. ( http://haskell.org/haskell-mode/ )
0.1 Download Version 2.1 (or later?)
0.2 Add to your .emacs

(add-to-list 'load-path "<The Directory Where You Downloaded haskell-mode>")
(autoload 'haskell-mode "haskell-mode"
  "Major mode for editing Haskell scripts." t)
(add-to-list 'auto-mode-alist '("\\.hs" . haskell-mode))
(add-hook 'haskell-mode-hook 'turn-on-haskell-font-lock)
(add-hook 'haskell-mode-hook 'turn-on-haskell-decl-scan)
(add-hook 'haskell-mode-hook 'turn-on-haskell-doc-mode)
(add-hook 'haskell-mode-hook 'turn-on-haskell-indent)
(add-hook 'haskell-mode-hook 'turn-on-haskell-ghci)

1. Check out and compile Agda2.
   For the detail, see XXX.

   Let us write <AGDA2-TOP> for the cvs working directory for your
   copy of Agda2.

2. Add the following to your .emacs

(add-to-list 'load-path "<AGDA2-TOP>/src/full/Interaction")
(autoload 'agda2-mode "agda2-mode" "Agda2 mode." t)
(add-to-list 'auto-mode-alist '("\\.ag2" . agda2-mode))
   ;; you may change the suffix "\\.ag2" to whatever you like.

3. Customize.
3.1. Restart emacs
3.2. Do
     M-x load-library<RETURN>agda2-mode<RETURN>
3.3. Do
     M-x customize-group<RETURN>agda2<RETURN>
3.4. In the customization buffer,
     set agda2-root-dir to <AGDA2-TOP>
3.5. click "save for future sessions"

4. Give a new modification time to the file

   <AGDA2-TOP>/src/full/Interaction/GhciTop.hs

   (by opening and re-saving it, or by doing "touch", for example)

5. Restart emacs again.
   Now opening a file XXX.ag2 (or whatever suffix you chose at Step 2)
   will start in agda2-mode.  It may take 5 or 10 seconds but it is normal.


Notes:

* If you have installed agda-mode for Agda1 before, ".agda" file
  may or may not start up in agda2-mode due to a mysterious bug around
  auto-mode.  If this happens, try exchanging the order in which agda-mode
  and agda2-mode are setup in your .emacs .

* If just opening an agda2 file freezes up your emacs, you might need to
  give up syntax highlighting.  Do
  M-x customize-group<RETURN>agda2<RETURN>
  and DELete `turn-on-agda2-font-lock' from `agda2-mode-hook'
