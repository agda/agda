;; agda2-mode.el --- Major mode for Agda2

;;;; cleaning up, just in case.
(when (fboundp 'dolist)
  (dolist (b (buffer-list))
    (with-current-buffer b
      (if (or (equal (buffer-name) "*ghci*") (eq major-mode 'agda2-mode))
          (kill-buffer b)))))
(if (featurep 'agda2) (unload-feature 'agda2))

;;;; Dependency

(require 'cl) ;  haskell-indent requires it anyway.
(or (fboundp 'cl-simple-expr-p) (load "cl-macs"))
(or (fboundp 'common-lisp-indent-function) (load "cl-indent"))
(set (make-local-variable 'lisp-indent-function) 'common-lisp-indent-function)
(require 'comint)
(require 'pp)
(require 'haskell-mode)
(require 'haskell-indent)
(require 'font-lock)
(unless (fboundp 'overlays-in) (load "overlay")) ; for Xemacs
(unless (fboundp 'propertize)                    ; for Xemacs 21.4
 (defun propertize (string &rest properties)
  "Return a copy of STRING with text properties added.
First argument is the string to copy.
Remaining arguments form a sequence of PROPERTY VALUE pairs for text
properties to add to the result."
  (let ((str (copy-sequence string)))
    (add-text-properties 0 (length str) properties str)
    str)))

;;;; Programming utilities

(defmacro agda2-protect (form &optional default)
  "Expands to (condition-case nil FORM (error DEFAULT))"
  `(condition-case nil ,form (error ,default)))
(put 'agda2-protect 'lisp-indent-function 0)
(defmacro agda2-let (varbind funcbind &rest body)
  "Expands to (let* VARBIND (labels FUNCBIND BODY...))"
  `(let* ,varbind (labels ,funcbind ,@body)))
(put 'agda2-let 'lisp-indent-function 2)

(defmacro agda2-undoable (&rest body)
  "Wrap BODY with `agda2-undo-list' book-keeping"
  `(if (buffer-file-name) ; aggda-mode and visiting, i.e. not generated.
       (let ((old-undo buffer-undo-list)
             (old-state agda2-buffer-state))
         (setq buffer-undo-list nil)
         ,@body
         (push (list buffer-undo-list old-undo old-state) agda2-undo-list)
         (setq buffer-undo-list nil))))

;;;; User options

(defgroup agda2 nil "User options for agda2-mode")
(defcustom agda2-root-dir "m:/Agda2"
  "The root of cvs Agda2 module working directory.  Customizing this takes
effect only after doing 'erase-customization' for `agda2-ghci-options' below"
  :type 'string :group 'agda2)

(defcustom agda2-ghci-options
  (let ((outdir (concat agda2-root-dir "/out/full")))
    (list
     (concat "-i" agda2-root-dir "/src/full")
     (concat "-i" outdir)
     (concat "-hidir " outdir)
     (concat "-odir  " outdir)
     "-I."
     "-Wall"
     "-Werror"
     "-fno-warn-missing-signatures"
     "-fno-warn-name-shadowing"
     "-fno-warn-simple-patterns"
     "-fno-warn-unused-matches"
     "-fno-warn-unused-binds"
     "-fno-warn-unused-imports"
     "-fno-warn-type-defaults"))
  "*The options for ghci to load `agda2-toplevel-module'."
  :type '(repeat string) :group 'agda2)

(defcustom agda2-toplevel-module "GhciTop"
  "*The name of the Agda2 toplevel module"
  :type 'string :group 'agda2)
  
(defcustom agda2-mode-hook '(turn-on-agda2-indent turn-on-agda2-font-lock)
  "*Hooks for agda2-mode.
Remove `turn-on-agda2-indent', `turn-on-agda2-font-lock' from here to disable
those features." :type 'hook :group 'agda2)

;;;; Global and buffer-local vars, initialization

(defvar agda2-mode-syntax-table
  (let ((tbl (make-syntax-table))
        (l  '(?{ "(}1" ?} "){4" ?-  ". 23"
              ?\\ "." ?_  "w"  ?\' "w" ?. "."  ?=  "."  ?: "." ?, "." )))
    (while l (modify-syntax-entry (pop l) (pop l) tbl)) tbl)
  "Syntax table used while in agda2 mode")
(defvar agda2-mode-map (copy-keymap haskell-mode-map) "Keymap for agda2-mode")
(defvar agda2-goal-map (make-sparse-keymap "Agda goal")
  "Keymap for agda2 goal menu")
(let ((l 
       '(
         (agda2-restart             "\C-c\C-x\C-c"  "Restart"               )
         (agda2-quit                "\C-c\C-q"      "Quit"                  )
         (agda2-load                "\C-c\C-x\C-b"  "Load"                  )
         (agda2-show-constraints    "\C-c\C-e"      "Show constraints"      )
         (agda2-show-goals          "\C-c\C-x\C-a"  "Show goals"            )
         (agda2-undo                "\C-c\C-u"      "Undo"                  )
         (agda2-text-state          "\C-c'"         "Text state"            )
         (agda2-next-goal           "\C-c\C-f"      "Next goal"             )
         (agda2-previous-goal       "\C-c\C-b"      "Previous goal"         )
         (agda2-give                "\C-c\C-g"  nil "Give"                  )
         (agda2-refine              "\C-c\C-r"  nil "Refine"                )
         (agda2-show-context        "\C-c|"     nil "Context"               )
         (agda2-infer-type          "\C-c:"     nil "Infer type"            )
         (agda2-infer-type-normalised "\C-c\C-x:" nil "Infer type (normalised)" )
         (agda2-submit-bug-report   nil             "Submit bug report"     )
         )))
  (define-key agda2-mode-map [menu-bar Agda2]
    (cons "Agda2" (make-sparse-keymap "Agda2")))
  (define-key agda2-mode-map [down-mouse-3]  'agda2-popup-menu-3)
  (dolist (d (reverse l))
    (let ((f (car d)) (k (cadr d)) (s1 (elt d 2)) (s2 (elt d 3)))
      (if k  (define-key agda2-mode-map k f))
      (if s1 (define-key agda2-mode-map
                 (vector 'menu-bar 'Agda2 (make-symbol s1)) (cons s1 f)))
      (if s2 (define-key agda2-goal-map
                 (vector (make-symbol s2)) (cons s2 f))))))
(defvar agda2-mode-abbrev-table nil "Abbrev table used while in agda2 mode")
(define-abbrev-table 'agda2-mode-abbrev-table ())
(defvar agda2-buffer  nil "Agda subprocess buffer.  Set in `agda2-restart'")
(defvar agda2-process nil "Agda subprocess.  Set in `agda2-restart'")

;; buffer locals
;; memo: agda2-undo should take care of buffer locals
(defvar agda2-buffer-state "Text"
  "State of an agda2-mode buffer.  \"Text\" or \"Type Correct\"")
(make-variable-buffer-local 'agda2-buffer-state)
(defvar agda2-undo-list nil
  "List of undo information produced at `agda2-undoable' and
consumed at `agda2-undo'.  It is a list of list
 \(undo-list for one agda2-action
   old buffer-undo-list before the action
   old agda2-buffer-state before the action\)")
(make-variable-buffer-local 'agda2-undo-list)

(defconst agda2-buffer-identification '((:eval agda2-buffer-state) ": %12b"))
(defconst agda2-help-address
  ""
  "Address accepting submissions of bug reports and questions")

;; Annotation for a goal
;; {! .... !}
;; ----------  overlay:    agda2-gn num, face highlight  , after-string num
;; -           text-props: agda2-gn num, intangible left , read-only
;;  -          text-props: invisible,    intangible left , read-only
;;         -   text-props: invisible,    intangible right, read-only
;;          -  text-props:               intangible right, read-only
;; Goal number agda2-gn is duplicated in overlay and text-prop so that
;; overlay can be re-made after undo.
;;
;; Char categories for {! ... !}
(flet ((stpl (c ps) (setplist c (append '(read-only t rear-nonsticky t
                                          intangible) ps))))
  (stpl 'agda2-delim1 '(left))
  (stpl 'agda2-delim2 '(left  invisible t))
  (stpl 'agda2-delim3 '(right invisible t))
  (stpl 'agda2-delim4 '(right)))


;;;; agda2-mode

(defun agda2-mode ()
 "Major mode for agda2 files.
  Special commands:
 \\{agda2-mode-map}"
 (interactive)
 (kill-all-local-variables)
 ;;(make-local-hook 'haskell-mode-hook)
 ;;(remove-hook 'haskell-mode-hook 'turn-on-haskell-font-lock 'local)
 ;;(remove-hook 'haskell-mode-hook 'turn-on-haskell-doc-mode 'local)
 (haskell-mode) (turn-off-haskell-font-lock) (turn-off-haskell-doc-mode)
 (use-local-map    agda2-mode-map)
 (set-syntax-table agda2-mode-syntax-table)
 (setq mode-name          "Agda2"
       major-mode         'agda2-mode
       local-abbrev-table agda2-mode-abbrev-table
       indent-tabs-mode   nil
       mode-line-buffer-identification agda2-buffer-identification)
 (let ((l '(comment-start      "{- "
            comment-end         " -}"
            comment-start-skip  "{-+ *"
            comment-column      32
            comment-multi-line  t
            max-specpdl-size    2600
            max-lisp-eval-depth 2800)))
   (while l (set (make-local-variable (pop l)) (pop l))))
 (agda2-restart)
 (force-mode-line-update)
 (run-hooks 'agda2-mode-hook))

(defun agda2-restart (&optional force)
  "Load agda2-toplevel-module to ghci"
  (interactive)
  (if (or force (not (eq 'run (agda2-process-status))))
    (save-excursion (let ((agda2-bufname "*ghci*"))
                      (agda2-protect (kill-buffer agda2-bufname))
                      (haskell-ghci-start-process nil)
                      (setq agda2-process  haskell-ghci-process
                            agda2-buffer   haskell-ghci-process-buffer
                            mode-name "Agda2 GHCi")
                      (rename-buffer agda2-bufname))))
  (apply 'agda2-go ":set" agda2-ghci-options)
  (agda2-go ":l" agda2-toplevel-module)
  (agda2-text-state))

;;;; Communicating with Agda2

(defun agda2-go (&rest args)
  "Send the list ARGS of strings to ghci, then
wait for output and execute responses, if any"
  (interactive)
  (unless (eq 'run (agda2-process-status))
    (error "Agda2 process is not running.  Please M-x agda2-restart"))
  (save-excursion
    (haskell-ghci-go (apply 'concat (agda2-intersperse " " args)) nil))
  (display-buffer agda2-buffer 'not-tihs-window)
  (let (response)
    (with-current-buffer haskell-ghci-process-buffer
      (haskell-ghci-wait-for-output)
      (setq response (buffer-substring-no-properties
                      (overlay-start comint-last-output-overlay)
                      (overlay-start comint-last-prompt-overlay))))
    (agda2-respond response)))

(defun agda2-goal-cmd (cmd &optional want ask &rest args)
  "When in a goal, send CMD, goal num and range, and strings ARGS to agda2.
WANT is an optional prompt.  When ASK is non-nil, use minibuffer."
  (multiple-value-bind (o g) (agda2-goal-at (point))
    (unless g (error "For this command, please place the cursor in a goal"))
    (let ((txt (buffer-substring-no-properties (+ (overlay-start o) 2)
                                               (- (overlay-end   o) 2))))
      (if (not want) (setq txt "")
          (when (or ask (string-match "\\`\\s *\\'" txt))
            (setq txt (read-string (concat want ": ") txt))
            (goto-char (+ (overlay-start o) 2))
            (insert txt)))
      (apply 'agda2-go cmd
             (format "%d" g)
             (agda2-goal-Range o)
             (agda2-string-quote txt) args))))

(defun agda2-respond (response)
  "Execute 'agda2_mode_code<sexp>' within RESPONSE string"
  (save-excursion
    (while (string-match "agda2_mode_code" response)
      (setq response (substring response (match-end 0)))
      (let ((inhibit-read-only t)
            (inhibit-point-motion-hooks t))
        (eval (read response))))))

;;;; User commands and response processing

(defun agda2-load ()
  "Load current buffer" (interactive)
  (agda2-go "cmd_load" (concat "\"" (buffer-file-name) "\"")))
(defun agda2-load-action (gs)
  "Annotate new goals GS in current buffer."
  (agda2-undoable
   (agda2-forget-all-goals)
   (agda2-annotate gs (point-min))
   (setq agda2-buffer-state "Type Checked")))

(defun agda2-give()
  "Give to the goal at point the expression in it" (interactive)
  (agda2-goal-cmd "cmd_give" "expression to give"))
(defun agda2-give-action (old-g paren new-gs)
  "Update the goal OLD-G with the expression in it and
annotate new goals NEW-GS"
  (agda2-undoable (agda2-update old-g paren new-gs)))

(defun agda2-refine ()
  "Refine the goal at point by the expression in it" (interactive)
  (agda2-goal-cmd "cmd_refine" "expression to refine"))

(defun agda2-show-goals()
  "Show all goals" (interactive)
  (agda2-go "cmd_metas"))
(defun agda2-show-constraints()
  "Show constraints" (interactive)
  (agda2-go "cmd_constraints"))

(defun agda2-text-state ()
  "UNDER CONSTRUCTION" (interactive)
  (dolist (o (overlays-in (point-min) (point-max)))
    (delete-overlay o))
  (agda2-go "ioTCM $ do putUndoStack []; resetState")
  (let ((old-undo buffer-undo-list)
        (inhibit-read-only t)
        (inhibit-point-motion-hooks t))
    (remove-text-properties
     (point-min) (point-max)
     '(category intangible read-only invisible agda2-gn))
    (setq agda2-undo-list  nil
          buffer-undo-list old-undo
          agda2-buffer-state "Text")
    (force-mode-line-update)))

(defun agda2-next-goal ()     "Go to the next goal, if any"     (interactive)
  (agda2-mv-goal 'next-single-property-change     'agda2-delim2 1 (point-min)))
(defun agda2-previous-goal () "Go to the previous goal, if any" (interactive)
  (agda2-mv-goal 'previous-single-property-change 'agda2-delim3 0 (point-max)))
(defun agda2-mv-goal (change delim adjust wrapped)
  (agda2-let ((inhibit-point-motion-hooks t))
      ((go (p) (while (and (setq p (funcall change p 'category))
                           (not (eq (get-text-property p 'category) delim))))
           (if p (goto-char (+ adjust p)))))
    (or (go (point)) (go wrapped) (message "No goals in the buffer"))))

(defun agda2-undo() "UNDERCONSTRUCTION: Undo" (interactive)
  (labels ((remake-goal(); remake overlays based on undone text prop
             (let ((p (point-min)))
               (dolist (o (overlays-in  p (point-max))) (delete-overlay o))
               (while (setq p (next-single-property-change p 'agda2-gn))
                 (when (get-text-property p 'agda2-gn)
                   (agda2-make-goal-B p))))))
    (cond (buffer-undo-list (setq buffer-undo-list
                                  (primitive-undo 2 buffer-undo-list)))
          (agda2-undo-list   (let ((undos (pop agda2-undo-list)))
                               (primitive-undo 10000 (car undos))
                               (agda2-go "cmd_undo")
                               (setq buffer-undo-list (cadr undos)
                                     agda2-buffer-state (caddr undos))
                               (force-mode-line-update)))
          (t (error "No further undo information (agda2)")))
    (remake-goal)))

(defun agda2-quit ()
  "Quit and clean up after agda2" (interactive)
  (agda2-protect (progn (haskell-ghci-go ":quit")
                        (kill-buffer agda2-buffer)
                        (kill-buffer (current-buffer)))))
(defun agda2-show-context ()
  "Show context of the goal at point" (interactive)
  (agda2-goal-cmd "cmd_context"))

(defun agda2-infer-type ()
  "Infer type of the goal at point" (interactive)
  (agda2-goal-cmd "cmd_infer B.Instantiated" "expression to type"))

(defun agda2-infer-type-normalised()
  "Infer normalised type of the goal at point" (interactive)
  (agda2-goal-cmd "cmd_infer B.Normalised" "expression to type"))
  
;;;;

(defun agda2-annotate (goals pos)
  "Find GOALS in the current buffer starting from POS and annotate them
with text-properties"
  (agda2-let (stk top)
      ((delims() (re-search-forward "[?]\\|[{][-!]\\|[-!][}]\\|--" nil t))
       (make(p)  (agda2-make-goal  p (point) (pop goals)))
       (err()    (error "Unbalanced \{- , -\} , \{\! , \!\}")))
    (save-excursion
      (goto-char pos)
      (while (and goals (delims))
        (labels ((c (s) (equal s (match-string 0))))
          (cond
           ((c "--") (end-of-line))
           ((c "{-") (push  nil          stk))
           ((c "{!") (push (- (point) 2) stk))
           ((c "-}") (unless (and stk (not (pop stk))) (err)))
           ((c "!}") (if (and stk (setq top (pop stk)))
                         (or stk (make top))
                       (err)))
           ((c "?")  (unless stk
                       (delete-char -1)(insert "{! !}")
                       (make (- (point) 5))))))))))

(defun agda2-make-goal (p q n)
  "Make a goal with number N at <P>{!...!}<Q>.  Assume the region is clean"
  (flet ((atp (x ps) (add-text-properties x (1+ x) ps)))
    (atp p       `(category agda2-delim1 agda2-gn ,n))
    (atp (1+ p)  '(category agda2-delim2))
    (atp (- q 2) '(category agda2-delim3))
    (atp (1- q)  '(category agda2-delim4))
    (agda2-make-goal-B p q n)))

(defun agda2-make-goal-B (p &optional q n)
  "Make a goal at <P>{!...!} assuming text-properties are already set"
  (or q (setq q (+ 2 (text-property-any p (point-max) 'intangible 'right))))
  (or n (setq n (get-text-property p 'agda2-gn)))
  (setq o (make-overlay p q nil t nil))
  (overlay-put o 'agda2-gn      n)
  (overlay-put o 'face         'highlight)
  (overlay-put o 'after-string (propertize (format "%s" n) 'face 'highlight)))

(defun agda2-update (old-g new-txt new-gs)
  "Update the goal OLD-G and annotate new goals NEW-GS.
NEW-TXT is a string to replace OLD-G, or `'paren', or `'no-paren'"
  (interactive)
  (multiple-value-bind (p q) (agda2-range-of-goal old-g)
    (if (not p) (message "ignoring an update for the missing goal %d" old-g)
        (save-excursion
          (agda2-forget-goal old-g)
          (if (stringp new-txt)
              ;; replace <p>{!...!}<q> as a rectangle
              (let ((indent (and (goto-char p) (current-column))))
                (delete-region p q) (insert new-txt)
                (while (re-search-backward "^" p t)
                  (insert-char ?  indent) (backward-char (1+ indent))))
              ;; else, remove braces from <p>{! !}<q> [and add parens]
              (flet ((doit (x y z) (goto-char x) (delete-char y)
                           (when (equal new-txt 'paren) (insert z))))
                (doit q -2 ")") (doit p 2 "(")))
          (agda2-annotate new-gs p)))))


;;;; Misc

(defun agda2-process-status ()
  "Status of agda2-buffer, or \"no process\""
  (agda2-protect (process-status agda2-process) "no process"))

(defun agda2-intersperse (sep xs) (interactive)
  (let(ys)(while xs (push (pop xs) ys)(push sep ys))(pop ys)(nreverse ys)))

(defun agda2-goal-Range (o)
  "Range of goal overlay O" (interactive)
  (format "(Range %s %s)"
          (agda2-mkPos (+ (overlay-start o) 2))
          (agda2-mkPos (- (overlay-end   o) 2))))

(defun agda2-mkPos (&optional p)
  "Position value of P or point" (interactive)
  (save-excursion
    (if p (goto-char p))
    (format "(Pn \"%s\" %d %d)" (buffer-file-name)
            (count-lines (point-min) (point)) (1+ (current-column)))))

(defun agda2-string-quote (s)
  "add escape to newlines, doublequote, etc. in string S"
  (let ((pp-escape-newlines t)) (pp-to-string s)))

(defun agda2-goal-at(pos)
  "Return (goal overlay, goal number) at POS, or nil"
  (let ((os (and pos (overlays-at pos))) o g)
    (while (and os (not(setq g (overlay-get (setq o (pop os)) 'agda2-gn)))))
    (if g (list o g))))

(defun agda2-goal-overlay (g)
  "Return overlay of the goal number G"
  (car(agda2-goal-at(text-property-any(point-min)(point-max) 'agda2-gn g))))

(defun agda2-range-of-goal (g)
  "the range of goal G"
  (let ((o (agda2-goal-overlay g)))
    (if o (list (overlay-start o) (overlay-end o)))))

(defun agda2-forget-goal (g)
  (let ((o (agda2-goal-overlay g)))
    (when o
      (remove-text-properties
       (overlay-start o) (overlay-end o)
       '(category intangible read-only invisible agda2-gn))
      (delete-overlay o))))

(defun agda2-forget-all-goals ()
  (let ((p (point-min)) g)
    (while (setq p (next-single-property-change p 'agda2-gn))
      (agda2-forget-goal (get-text-property p 'agda2-gn)))))
  

(defun turn-on-agda2-indent ()
  "A copy of `turn-on-haskell-indent' with additional off-side words"
  (interactive)
  (labels ((setl (var val) (set (make-local-variable var) val)))
    (setl 'indent-line-function 'haskell-indent-cycle)
    (setl 'haskell-indent-off-side-keywords-re
          "\\<\\(do\\|let\\|of\\|where\\|sig\\|struct\\)\\>[ \t]*"))
  (local-set-key "\177"  'backward-delete-char-untabify)
  (local-set-key "\t"    'haskell-indent-cycle)
  (setq haskell-indent-mode t)
  (run-hooks 'haskell-indent-hook))
(defalias 'turn-off-agda2-indent 'turn-off-haskell-indent)

;;;; Font-lock support

(defvar agda2-re-font-lock nil)
(defvar agda2-re-vars nil)
(defvar agda2-re-param nil)
(defvar agda2-re-in-param nil)
(defvar agda2-re-dc nil)
(labels
    ((c  (&rest rs)   (apply 'concat rs))
     (g  (r)          (c "\\(" r "\\)"))
     (w  (r)          (c "\\<" r "\\>"))
     (p  (r)          (c r "+"))
     (t  (r)          (c r "*"))
     (o  (r &rest rs) (apply 'c r (mapcar #'(lambda(x) (c "\\|" x)) rs))))
  (let* ((spc    (t "\\s "))
         (keywd  (g (regexp-opt '("abstract" "case" "concrete" "data" "in"
                                 "let" "of" "open" "package" "private"
                                 "public" "sig" "struct" "use" "mutual"
                                 "postulate" "idata" "where"
                                 "class" "exports" "instance"
                                 "CHEAT" "external"
                                  "infixr" "infix" "infixl"
                                 ))))
         (op     (c "("(p(g(o "\\s_" "\\s.")))")"))
         (ide    (g (o "\\sw+" op)))
         (ides   (t(g(c spc "," spc "[|!]?" spc ide))))
         (sor    (g (o "Set\\b" "Type\\b"))))
    (setq agda2-re-font-lock (o (g "--.*$") (w (o sor keywd)) ide)
          agda2-re-vars      (c "\\=" ides)
          agda2-re-param     (c spc "[({][|!]?" ide ides spc ":")
          agda2-re-in-param  (c "[({][|!]?" ide ides spc "\\=")
          agda2-re-dc        (c spc (g (o ":" "where"))))))
(defvar agda2-nil6 (make-list 6 nil))
(defvar agda2-nil8 (make-list 8 nil))
;; `agda2-matcher' returns one-liner comment as 1st subexpression match
;;                        "Set\\|Type"         2nd
;;                        other keywords       3rd
;;                        bound ide(approx)    4th
;;                        defined ide(approx)  5th
;; Approx bound   ide is recognised by "(...,ide,...:"
;; Approx defined ide is recognised by "ide(...)...(...):"
;; This is way too slow.  Full blown parsing may actually be faster..
(defun agda2-matcher (&optional end)
  (unless end (setq end (point-max)))
  (let (md ok)
    (while (and (not ok) (re-search-forward agda2-re-font-lock end t))
      (setq md (match-data)
            ok (or (elt md 2) (elt md 4) (elt md 6)
                   (progn (re-search-forward agda2-re-vars end t)
                          (agda2-protect (while (looking-at agda2-re-param)
                                          (forward-sexp)))
                          (when  (looking-at agda2-re-dc)
                            (setcdr (cdr md) nil)
                            (set-match-data
                             (append md (if (re-search-backward
                                             agda2-re-in-param nil t)
                                            agda2-nil6 agda2-nil8) md))
                            t))))
      (goto-char (cadr md)))
    ok))
(defconst agda2-font-lock-keywords
   '((agda2-matcher
      (0 (cond ((match-beginning 1) font-lock-comment-face)
               ((match-beginning 2) font-lock-type-face)
               ((match-beginning 3) font-lock-keyword-face)
               ((match-beginning 4) font-lock-variable-name-face)
               ((match-beginning 5) font-lock-function-name-face)) nil t))))

(defun turn-on-agda2-font-lock ()
  "Set `font-lock-defaults' for agda2 code and turn on font lock.
See also `agda2-fontify-included-files'"
  (interactive)
  (set (make-local-variable 'font-lock-defaults)
       '(agda2-font-lock-keywords nil nil nil))
  (turn-on-font-lock))
