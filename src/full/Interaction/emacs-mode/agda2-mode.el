;; agda2-mode.el --- Major mode for Agda2

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Dependency

(require 'cl) ;  haskell-indent requires it anyway.
(or (fboundp 'cl-simple-expr-p) (load "cl-macs"))
(or (fboundp 'common-lisp-indent-function) (load "cl-indent"))
(set (make-local-variable 'lisp-indent-function) 'common-lisp-indent-function)
(require 'comint)
(require 'pp)
(require 'eri)
(require 'agda2-highlight)
(require 'haskell-indent)
(require 'haskell-ghci)
;; due to a bug in haskell-mode-2.1
(setq haskell-ghci-mode-map (copy-keymap comint-mode-map))
; Load filladapt, if it is installed.
(condition-case nil
    (require 'filladapt)
  (error nil))
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
(unless (fboundp 'run-mode-hooks)
  (fset 'run-mode-hooks 'run-hooks))  ; For Emacs versions < 21.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Programming utilities

(defmacro agda2-protect (form &optional default)
  "Expands to (condition-case nil FORM (error DEFAULT))"
  `(condition-case nil ,form (error ,default)))
(put 'agda2-protect 'lisp-indent-function 0)
(defmacro agda2-let (varbind funcbind &rest body)
  "Expands to (let* VARBIND (labels FUNCBIND BODY...))"
  `(let* ,varbind (labels ,funcbind ,@body)))
(put 'agda2-let 'lisp-indent-function 2)

; More undo stuff further down.

(defmacro agda2-undoable (&rest body)
  "Wrap BODY with `agda2-undo-list' book-keeping (if `agda2-undo-kind'
is `agda')."
  (let ((old-undo  (make-symbol "old-undo"))
        (old-state (make-symbol "old-state")))
  `(if (eq agda2-undo-kind 'agda)
      (if (buffer-file-name) ; aggda-mode and visiting, i.e. not generated.
           (let ((,old-undo buffer-undo-list)
                 (,old-state agda2-buffer-state))
             (setq buffer-undo-list nil)
             ,@body
             (push (list buffer-undo-list ,old-undo ,old-state)
                   agda2-undo-list)
             (setq buffer-undo-list nil)))
    ,@body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; User options

(defgroup agda2 nil
  "Major mode for interactively developing Agda programs."
  :group 'languages)

(defcustom agda2-include-dirs
  (list ".")
  "*The directories Agda uses to search for files (relative to the
top-level of the current project)."
  :type '(repeat directory)
  :group 'agda2)

(defcustom agda2-ghci-options
  (list "-package Agda")
  "*These options are set in GHCi before `agda2-toplevel-module' is
loaded. Note that only dynamic options can be set using this
variable."
  :type '(repeat string)
  :group 'agda2)

(defcustom agda2-toplevel-module "Interaction.GhciTop"
  "*The name of the Agda2 toplevel module"
  :type 'string :group 'agda2)

(defcustom agda2-mode-hook
  '(agda2-fix-ghci-for-windows)
  "*Hooks for agda2-mode."
  :type 'hook :group 'agda2)

(defcustom agda2-indentation
  'eri
  "*The kind of indentation used in `agda2-mode'."
  :type '(choice (const :tag "Haskell" haskell)
                 (const :tag "Extended relative" eri)
                 (const :tag "None" nil))
  :group 'agda2)

(defcustom agda2-undo-kind
  'emacs
  "*The kind of undo functionality used in `agda2-mode'. It may be
necessary to restart Agda mode after changing this variable."
  :type '(choice (const :tag "Emacs (just text)" emacs)
                 (const :tag "Agda (also the type-checking state)" agda))
  :group 'agda2)

(defcustom agda2-change-default-font t
  "Should the Agda mode change the default font of the current
frame when activated?"
  :type '(choice (const :tag "Change" t)
                 (const :tag "Don't change" nil))
  :group 'agda2)

(defcustom agda2-fontset-spec
  (concat
   "-misc-fixed-medium-r-normal-*-15-*-*-*-*-*-fontset-agda2"
   (cond
    ((eq window-system 'x) "")
    ((eq window-system 'w32) ",
    ascii:-Misc-Fixed-Medium-R-Normal--15-140-75-75-C-90-ISO8859-1,
    latin-iso8859-2:-*-Fixed-*-r-*-*-15-*-*-*-c-*-iso8859-2,
    latin-iso8859-3:-*-Fixed-*-r-*-*-15-*-*-*-c-*-iso8859-3,
    latin-iso8859-4:-*-Fixed-*-r-*-*-15-*-*-*-c-*-iso8859-4,
    cyrillic-iso8859-5:-*-Fixed-*-r-*-*-15-*-*-*-c-*-iso8859-5,
    greek-iso8859-7:-*-Fixed-*-r-*-*-15-*-*-*-c-*-iso8859-7,
    latin-iso8859-9:-*-Fixed-*-r-*-*-15-*-*-*-c-*-iso8859-9,
    mule-unicode-0100-24ff:-Misc-Fixed-Medium-R-Normal--15-140-75-75-C-90-ISO10646-1,
    mule-unicode-2500-33ff:-Misc-Fixed-Medium-R-Normal--15-140-75-75-C-90-ISO10646-1,
    mule-unicode-e000-ffff:-Misc-Fixed-Medium-R-Normal--15-140-75-75-C-90-ISO10646-1,
    japanese-jisx0208:-JIS-Fixed-Medium-R-Normal--16-150-75-75-C-160-JISX0208.1983-0,
    japanese-jisx0208-1978:-Misc-Fixed-Medium-R-Normal--16-150-75-75-C-160-JISC6226.1978-0,
    japanese-jisx0212:-Misc-Fixed-Medium-R-Normal--16-150-75-75-C-160-JISX0212.1990-0,
    latin-jisx0201:-*-*-medium-r-normal-*-16-*-*-*-c-*-jisx0201*-*,
    katakana-jisx0201:-Sony-Fixed-Medium-R-Normal--16-120-100-100-C-80-JISX0201.1976-0,
    thai-tis620:-Misc-Fixed-Medium-R-Normal--24-240-72-72-C-120-TIS620.2529-1,
    lao:-Misc-Fixed-Medium-R-Normal--24-240-72-72-C-120-MuleLao-1,
    tibetan:-TibMdXA-fixed-medium-r-normal--16-160-72-72-m-160-MuleTibetan-0,
    tibetan-1-column:-TibMdXA-fixed-medium-r-normal--16-160-72-72-m-80-MuleTibetan-1,
    korean-ksc5601:-Daewoo-Mincho-Medium-R-Normal--16-120-100-100-C-160-KSC5601.1987-0,
    chinese-gb2312:-ISAS-Fangsong ti-Medium-R-Normal--16-160-72-72-c-160-GB2312.1980-0,
    chinese-cns11643-1:-HKU-Fixed-Medium-R-Normal--16-160-72-72-C-160-CNS11643.1992.1-0,
    chinese-big5-1:-ETen-Fixed-Medium-R-Normal--16-150-75-75-C-160-Big5.ETen-0,
    chinese-big5-2:-ETen-Fixed-Medium-R-Normal--16-150-75-75-C-160-Big5.ETen-0")))
  "*The \"fontset-agda2\" fontset is created based on this string,
provided that `window-system' is x or w32. The default font of
the current frame is changed to \"fontset-agda2\" when the Agda2
mode is activated.

Note that the text \"fontset-agda2\" has to be part of the
string (in a certain way; see the default setting) in order for the
agda2 fontset to be created properly.

Note also that the default setting may not work unless suitable
fonts are installed on your system. Refer to the README and
README_WINDOWS files accompanying the Agda distribution for
details.

Note finally that you have to reload the Agda2 library if you
want settings to this variable to take effect."
  :group 'agda2
  :type 'string)

(if (memq window-system '(x w32))
  (create-fontset-from-fontset-spec agda2-fontset-spec))

(defun agda2-fix-ghci-for-windows ()
  (if (string-match "windows" system-configuration)
      (setq haskell-ghci-program-name "ghc"
            haskell-ghci-program-args '("--interactive" "-package lang"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Global and buffer-local vars, initialization

(defvar agda2-mode-syntax-table
  (let ((tbl (make-syntax-table))
        (l  '(?{ "(}1n" ?} "){4n" ?-  "_ 123b" ?\n "> b"
              ?\\ "." ?_  "w"  ?\' "w" ?. "."  ?=  "."  ?: "." ?, "." )))
    (while l (modify-syntax-entry (pop l) (pop l) tbl)) tbl)
  "Syntax table used while in agda2 mode")
(defvar agda2-mode-map (make-sparse-keymap "Agda mode") "Keymap for agda2-mode")
(defvar agda2-goal-map (make-sparse-keymap "Agda goal")
  "Keymap for agda2 goal menu")
(let ((l
       `(
         (agda2-load                               "\C-c\C-x\C-l"     "Load")
         (agda2-text-state                         "\C-c\C-x\C-d"     "Deactivate Agda")
         (agda2-quit                               "\C-c\C-x\C-q"     "Quit")
         (agda2-restart                            "\C-c\C-x\C-r"     "Restart")
         (agda2-display-implicit-arguments         "\C-c\C-x\C-h"     "Toggle display of hidden arguments")
         (agda2-highlight-reload-or-clear          "\C-c\C-x\C-s"     "Reload syntax highlighting information")
         (agda2-show-constraints                   ,(kbd "C-c C-=")   "Show constraints")
         (agda2-solveAll                           ,(kbd "C-c C-!")   "Solve constraints")
         (agda2-show-goals                         ,(kbd "C-c C-?")   "Show goals")
         (agda2-next-goal                          "\C-c\C-f"         "Next goal")      ; Forward.
         (agda2-previous-goal                      "\C-c\C-b"         "Previous goal")  ; Back.
         (agda2-undo                               "\C-c\C-u"         "Undo")
         (agda2-undo                               "\C-_"             "Undo")
         (agda2-infer-type-maybe-toplevel          nil                "Infer (deduce) type")
         (agda2-infer-type-toplevel-normalised     nil                "Infer type (normalised)")
         (agda2-compute-normalised-maybe-toplevel  nil                "Compute normal form")
         (agda2-give                               ,(kbd "C-c C-SPC") nil "Give")
         (agda2-refine                             "\C-c\C-r"         nil "Refine")
         (agda2-make-case                          "\C-c\C-c"         nil "Case")
         (agda2-goal-type                          "\C-c\C-t"         nil "Goal type")
         (agda2-goal-type-normalised               nil                nil "Goal type (normalised)")
         (agda2-show-context                       "\C-c\C-e"         nil "Context (environment)")
         (agda2-show-context-normalised            nil                nil "Context (normalised)")
         (agda2-infer-type-maybe-toplevel          "\C-c\C-d"         nil "Infer (deduce) type")
         (agda2-infer-type-normalised              nil                nil "Infer type (normalised)")
         (agda2-goal-and-infer                     ,(kbd "C-c C-.")   nil "Goal type and inferred type")
         (agda2-goal-and-infer-normalised          nil                nil "Goal type and inferred type (normalised)")
         (agda2-compute-normalised-maybe-toplevel  "\C-c\C-n"         nil "Compute normal form")
         (agda2-indent                ,(kbd "TAB"))
         (agda2-indent-reverse        [S-iso-lefttab])
         (agda2-indent-reverse        [S-lefttab])
         (agda2-indent-reverse        [S-tab])
         (agda2-goto-definition-mouse [mouse-2])
         (mouse-face [follow-link])  ; Enables using mouse-1 to click on links in Emacs 22.
         (agda2-goto-definition-keyboard "\M-.")
         (agda2-go-back                  "\M-*")
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

;; Some buffer locals
(defvar agda2-buffer-state "Text"
  "State of an agda2-mode buffer.  \"Text\" or \"Type Correct\"")
(make-variable-buffer-local 'agda2-buffer-state)

(defconst agda2-buffer-identification
  '((:eval agda2-buffer-state)
    ": "
    (:eval (let ((b (copy-sequence (buffer-name))))
             (put-text-property 0 (length b)
                                'face '(:weight bold)
                                b)
             (substring b 0 (min (length b) 30))))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; agda2-mode

(defun agda2-mode ()
 "Major mode for agda2 files.

Note that when this mode is activated the default font of the
current frame is changed to \"fontset-agda2\" (see
`agda2-fontset-spec'). The reason is that Agda programs often use
mathematical symbols and other Unicode characters, so we try to
provide a suitable default font setting, which can display many
of the characters encountered. If you prefer to use your own
settings, change the setting of `agda2-change-default-font'.

Special commands:
\\{agda2-mode-map}"
 (interactive)
 (kill-all-local-variables)
 (use-local-map    agda2-mode-map)
 (set-syntax-table agda2-mode-syntax-table)
 (setq mode-name          "Agda2"
       major-mode         'agda2-mode
       local-abbrev-table agda2-mode-abbrev-table
       indent-tabs-mode   nil
       mode-line-buffer-identification agda2-buffer-identification)
 (let ((l '(max-specpdl-size    2600
            max-lisp-eval-depth 2800)))
   (while l (set (make-local-variable (pop l)) (pop l))))
 (if agda2-change-default-font
     (set-frame-font "fontset-agda2"))
 (agda2-indent-setup)
 (agda2-highlight-setup)
 (agda2-comments-and-paragraphs-setup)
 (agda2-restart)
 (force-mode-line-update)
 (run-mode-hooks 'agda2-mode-hook))

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
                      (set-buffer-file-coding-system 'utf-8)
		      (set-buffer-process-coding-system 'utf-8 'utf-8)
                      (rename-buffer agda2-bufname))))
  (apply 'agda2-go ":set" agda2-ghci-options)
  (agda2-go ":mod +" agda2-toplevel-module)
  (agda2-text-state)
  (agda2-highlight-reload))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Communicating with Agda2

(defun agda2-go (&rest args)
  "Send the list ARGS of strings to ghci, then
wait for output and execute responses, if any"
  (interactive)
  (unless (eq 'run (agda2-process-status))
    ; Try restarting automatically, but only once, in case there is
    ; some major problem.
    (agda2-restart)
    (unless (eq 'run (agda2-process-status))
      (error "Agda2 process is not running.  Please M-x agda2-restart")))
  (save-excursion
    (haskell-ghci-go (apply 'concat (agda2-intersperse " " args)) nil))
  ;;(display-buffer agda2-buffer 'not-tihs-window)
  (let (response)
    (with-current-buffer haskell-ghci-process-buffer
      (haskell-ghci-wait-for-output)
      ; Note that the following code may be prone to race conditions
      ; (make-temp-file returns a filename, not an open file). This is
      ; not likely to be a problem, though.
      (let ((tempfile (make-temp-file "agda2-mode")))
        (unwind-protect
            (progn
              (comint-write-output tempfile)
              (with-temp-buffer
                (insert-file-contents tempfile)
                (setq response (buffer-substring-no-properties
                                (point-min) (point-max)))))
          (delete-file tempfile))))
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
            (setq txt (read-string (concat want ": ") txt))))
      (apply 'agda2-go cmd
             (format "%d" g)
             (agda2-goal-Range o)
             (agda2-string-quote txt) args))))

(defun agda2-respond (response)
  "Execute 'agda2_mode_code<sexp>' within RESPONSE string"
    (while (string-match "agda2_mode_code" response)
      (setq response (substring response (match-end 0)))
      (let ((inhibit-read-only t)
            (inhibit-point-motion-hooks t))
        (eval (read response)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; User commands and response processing

(defun agda2-load ()
  "Load current buffer"
  (interactive)
  (agda2-go "cmd_load"
            (agda2-string-quote (buffer-file-name))
            (agda2-list-quote agda2-include-dirs)
            ))

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

(defun agda2-make-case ()
  "Refine the pattern var given in the goal. Assumes that
<clause> = {!<var>!} is on one line"
  (interactive)
  (agda2-goal-cmd "cmd_make_case" "partten var to case"))

(defun agda2-make-case-action (newcls)
  "Replace the line at point with new clauses NEWCLS and reload"
  (agda2-undoable
   (agda2-forget-all-goals);; we reload later anyway.
   (let* ((p0 (point))
          (p1 (goto-char (agda2-decl-beginning)))
          (indent (current-column))
          cl)
     (goto-char p0)
     (re-search-forward "!}" (line-end-position) 'noerr)
     (delete-region p1 (point))
     (while (setq cl (pop newcls))
       (insert cl)
       (if newcls (insert "\n" (make-string indent ?  ))))
     (goto-char p1)))
  (agda2-load)
  (if (eq agda2-undo-kind 'agda)
      (progn
        ;; merge two actions' undo
        (let ((load-undo (car  agda2-undo-list))
              (case-undo (cadr agda2-undo-list))
              (rest-undo (cddr agda2-undo-list)))
          (setq agda2-undo-list (cons (list (append (car load-undo) (car case-undo))
                                            (cadr case-undo)
                                            (elt  case-undo 2))
                                      rest-undo))))))

(defun agda2-info-action (name text)
  "Insert TEXT into the Agda info buffer, display it, and display NAME
in the buffer's mode line."
  (interactive)
  (with-current-buffer (get-buffer-create "*Agda2 information*")
    (erase-buffer)
    (insert text)
    (goto-char (point-min))
    (put-text-property 0 (length name) 'face '(:weight bold) name)
    (setq mode-line-buffer-identification name)
    (save-selected-window
      (pop-to-buffer (current-buffer) 'not-this-window 'norecord)
      (shrink-window
       (- (window-height)
          (min (/ (frame-height) 2)
               (max window-min-height
                    (1+ (count-lines (point-min) (point-max))))))))))

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
  (agda2-go "cmd_reset")
  (let ((inhibit-read-only t) (inhibit-point-motion-hooks t))
    (let ((buffer-undo-list
           (if (eq agda2-undo-kind 'agda) nil buffer-undo-list)))
      (agda2-no-modified-p 'remove-text-properties
       (point-min) (point-max)
       '(category intangible read-only invisible agda2-gn)))
    (if (eq agda2-undo-kind 'agda)
        (agda2-flatten-undo))
    (setq agda2-buffer-state "Text")
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

(defun agda2-quit ()
  "Quit and clean up after agda2" (interactive)
  (agda2-protect (progn (kill-buffer agda2-buffer)
                        (kill-buffer (current-buffer)))))
 
(defmacro agda2-maybe-normalised (name comment cmd prompt)
  "This macro constructs two functions NAME and NAME-normalised, using
COMMENT to build the functions' comments. The function NAME takes a
prefix argument which tells whether it should normalise types or not
when running CMD (through `agda2-goal-cmd'; PROMPT, if non-nil, is
used as the goal command prompt)."
  (let ((eval (make-symbol "eval")))
  `(progn
     (defun ,name (&optional normalise)
       ,(concat comment ".

With a prefix argument the result is normalised.")
       (interactive "P")
       (let ((,eval (if normalise "Normalised" "Instantiated")))
         (agda2-goal-cmd (concat ,cmd " Interaction.BasicOps." ,eval)
                         ,prompt)))

     (defun ,(intern (concat (symbol-name name) "-normalised")) ()
       ,(concat comment " (normalised).")
       (interactive)
       (,name t))
     )))

(defmacro agda2-maybe-normalised-toplevel (name comment cmd prompt)
  "This macro constructs two functions NAME and NAME-normalised, using
COMMENT to build the functions' comments. The function NAME takes a
prefix argument which tells whether it should normalise types or not
when running CMD (through `agda2-go'; the string PROMPT is
used as the goal command prompt)."
  (let ((eval (make-symbol "eval")))
  `(progn
     (defun ,name (normalise expr)
       ,(concat comment ".

With a prefix argument the result is normalised.")
       (interactive ,(concat "P\nM" prompt ": "))
       (let ((,eval (if normalise "Normalised" "Instantiated")))
         (agda2-go (concat ,cmd " Interaction.BasicOps." ,eval " "
                           (agda2-string-quote expr)))))

     (defun ,(intern (concat (symbol-name name) "-normalised")) (expr)
       ,(concat comment ".

The result is normalised.")
       (interactive ,(concat "M" prompt ": "))
       (,name t expr))
     )))

(agda2-maybe-normalised
 agda2-goal-type
 "Show the type of the goal at point"
 "cmd_goal_type"
 nil)

(agda2-maybe-normalised
 agda2-infer-type
 "Infer the type of the goal at point"
 "cmd_infer"
 "expression to type")

(agda2-maybe-normalised-toplevel
   agda2-infer-type-toplevel
   "Infers the type of the given expression. The scope used for
the expression is that of the last point inside the current
top-level module"
   "cmd_infer_toplevel"
   "Expression")

(defun agda2-infer-type-maybe-toplevel ()
  "Infers the type of the given expression, using the
scope of the current goal or, if point is not in a goal, the
top-level scope."
  (interactive)
  (if (agda2-goal-at (point))
      (call-interactively 'agda2-infer-type)
    (call-interactively 'agda2-infer-type-toplevel)))

(agda2-maybe-normalised
 agda2-goal-and-infer
 "Shows the type of the goal at point and infers the type of the
given expression"
 "cmd_goal_type_infer"
 "expression to type")

(agda2-maybe-normalised
 agda2-show-context
 "Show the context of the goal at point"
 "cmd_context"
 nil)

(defun agda2-solveAll ()
  "Solve all goals that are internally already instantiated" (interactive)
  (agda2-go "cmd_solveAll" ))

(defun agda2-solveAll-action (iss)
  (save-excursion
    (while iss
      (let* ((g (pop iss)) (txt (pop iss)))
        (agda2-replace-goal g txt)
        (agda2-goto-goal g)
        (agda2-give)))))

(defun agda2-compute-normalised ()
  "Compute the normal form of exp in the goal at point"
  (interactive)
  (agda2-goal-cmd "cmd_compute Interaction.BasicOps.Normalised"
                  "expression to normalise"))

(defun agda2-compute-normalised-toplevel (expr)
  "Computes the normal form of the given expression. The scope used for
the expression is that of the last point inside the current
top-level module."
  (interactive "MExpression: ")
  (agda2-go (concat "cmd_compute_toplevel "
                    (agda2-string-quote expr))))

(defun agda2-compute-normalised-maybe-toplevel ()
  "Computes the normal form of the given expression, using the
scope of the current goal or, if point is not in a goal, the
top-level scope."
  (interactive)
  (if (agda2-goal-at (point))
      (call-interactively 'agda2-compute-normalised)
    (call-interactively 'agda2-compute-normalised-toplevel)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;

(defun agda2-annotate (goals pos)
  "Find GOALS in the current buffer starting from POS and annotate them
with text-properties"

  (agda2-let (stk top (inhibit-point-motion-hooks t))
      ((delims() (re-search-forward "[?]\\|[{][-!]\\|[-!][}]\\|--" nil t))
       (is-lone-questionmark ()
          (save-excursion
            (save-match-data
                (backward-char 3)
                (looking-at
                 "\\({!\\|.{\\|(\\|.\\s \\)[?]\\(\\s \\|)\\|}\\|!}\\|$\\)"))))
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
           ((c "?")  (progn
                       (when (and (not stk) (is-lone-questionmark))
                         (delete-char -1)(insert "{! !}")
                         (make (- (point) 5)))))))))))

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
          (cond ((stringp new-txt)
                 (agda2-replace-goal old-g new-txt))
                ((equal new-txt 'paren)
                 (goto-char (- q 2)) (insert ")")
                 (goto-char (+ p 2)) (insert "(")))
          (agda2-forget-goal old-g 'remove-braces)
          (agda2-annotate new-gs p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
    (format "(Pn \"%s\" %d %d %d)" (buffer-file-name)
            (point) (count-lines (point-min) (point)) (1+ (current-column)))))

(defun agda2-char-quote (c)
  "Converts non-ASCII characters to the \\xNNNN notation used in
Haskell strings. (The characters are actually rendered as
\"\\xNNNN\\&\", i.e. followed by a \"null character\", to avoid
problems if they are followed by digits.) ASCII characters (code
points < 128) are converted to singleton strings."
  (if (< c 128)
      (list c)
    (append (format "\\x%x\\&" (encode-char c 'ucs)) nil)))

(defun agda2-string-quote (s)
  "Escape newlines, double quotes, etc. in the string S, add
surrounding double quotes, and convert non-ASCII characters to the \xNNNN
notation used in Haskell strings."
  (let ((pp-escape-newlines t))
    (mapconcat 'agda2-char-quote (pp-to-string s) "")))

(defun agda2-list-quote (strings)
  "Converts a list of strings into a string representing a Haskell
list containing the strings."
  (concat "[" (mapconcat 'agda2-string-quote strings ", ") "]"))

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

(defun agda2-goto-goal (g)
  (let ((p (+ 2 (car (agda2-range-of-goal g)))))
    (if p (goto-char p))))

(defun agda2-replace-goal (g newtxt)
  "Replace the content of goal G with newtxt" (interactive)
  (save-excursion
    (multiple-value-bind (p q) (agda2-range-of-goal g)
      (setq p (+ p 2) q (- q 2))
      (let ((indent (and (goto-char p) (current-column))))
        (delete-region p q) (insert newtxt)
        (while (re-search-backward "^" p t)
          (insert-char ?  indent) (backward-char (1+ indent)))))))

(defun agda2-forget-goal (g &optional remove-braces)
  (multiple-value-bind (p q) (agda2-range-of-goal g)
    (let ((o (agda2-goal-overlay g)))
      (remove-text-properties p q
        '(category intangible read-only invisible agda2-gn))
      (when remove-braces
        (delete-region (- q 2) q)
        (delete-region p (+ p 2)))
      (delete-overlay o))))

(defun agda2-forget-all-goals ()
  (let ((p (point-min)))
    (while (setq p (next-single-property-change p 'agda2-gn))
      (agda2-forget-goal (get-text-property p 'agda2-gn)))))


(defun agda2-decl-beginning ()
  "Find the beginning point of the declaration containing the point. To do: dealing with semicolon separated decls."
  (interactive)
  (save-excursion
    (let* ((pEnd (point))
           (pDef (progn (goto-char (point-min))
                        (re-search-forward "\\s *" pEnd t)))
           (cDef (current-column)))
      (while (re-search-forward
              "where\\(\\s +\\)\\S \\|^\\(\\s *\\)\\S " pEnd t)
        (if (match-end 1)
            (setq pDef (goto-char (match-end 1))
                  cDef (current-column))
          (goto-char (match-end 2))
          (if (>= cDef (current-column))
              (setq pDef (point)
                    cDef (current-column))))
        (forward-char))
      (goto-char pDef)
      (if (equal (current-word) "mutual")
          (or (match-end 2) (match-end 1))
        pDef))))

(defun agda2-beginning-of-decl ()
  (interactive)
  (goto-char (agda2-decl-beginning)))

(defun agda2-no-modified-p (func &rest args)
  "call FUNC without affecting the buffer-modified flag."
  (interactive)
  (let ((old-buffer-modified (buffer-modified-p)))
    (apply func args)
    (set-buffer-modified-p old-buffer-modified)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Undo

(defun agda2-undo ()
  "Undo something. The result of executing this function depends on
the setting of `agda2-undo-kind'."
  (interactive)
  (cond ((eq agda2-undo-kind 'agda)  (agda2-agda-undo))
        ((eq agda2-undo-kind 'emacs) (undo))))

;; memo: agda2-agda-undo should take care of buffer locals
(defvar agda2-undo-list nil
  "List of undo information produced at `agda2-undoable' and
consumed at `agda2-agda-undo'.  It is a list of list
 \(undo-list for one agda2-action
   old buffer-undo-list before the action
   old agda2-buffer-state before the action\)")
(make-variable-buffer-local 'agda2-undo-list)

(defun agda2-agda-undo() "UNDERCONSTRUCTION: Undo" (interactive)
  (labels ((remake-goal()  ; remake overlays based on undone text prop
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

(defun agda2-flatten-undo ()
  "Flatten agda2-undo-list onto buffer-undo-list,
ignoring text-property undos."
  (let (flat-undo)
    (dolist (au agda2-undo-list)
      (dolist (u (car au))
        (cond
          ((and (listp u) (listp (cdr u))
                (null (car u))
                (or (equal 'category (cadr u))
                    (equal 'agda2-gn (cadr u))))
           'ignore)
          ((and (listp u) (stringp (car u)))
           (set-text-properties 0 (length (car u))
                                '(category nil agda2-gn nil)
                                (car u))
           (push u flat-undo))
          (t (push u flat-undo))))
      (setq flat-undo (append (reverse (cadr au)) flat-undo)))
    (setq buffer-undo-list (append buffer-undo-list (reverse flat-undo))
          agda2-undo-list nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Indentation

(defun agda2-indent ()
  "This is what happens when TAB is pressed. Depends on the setting of
`agda2-indentation'."
  (interactive)
  (cond ((eq agda2-indentation 'haskell) (haskell-indent-cycle))
        ((eq agda2-indentation 'eri) (eri-indent))))

(defun agda2-indent-reverse ()
  "This is what happens when S-TAB is pressed. Depends on the setting
of `agda2-indentation'."
  (interactive)
  (cond ((eq agda2-indentation 'eri) (eri-indent-reverse))))

(defun agda2-indent-setup ()
  "Sets up and starts the indentation subsystem. Depends on the
setting of `agda2-indentation'."
  (interactive)
  (cond ((eq agda2-indentation 'haskell)
         (labels ((setl (var val) (set (make-local-variable var) val)))
           (setl 'indent-line-function 'haskell-indent-cycle)
           (setl 'haskell-indent-off-side-keywords-re
                 "\\<\\(do\\|let\\|of\\|where\\|sig\\|struct\\)\\>[ \t]*"))
         (local-set-key "\177"  'backward-delete-char-untabify)
         (set (make-local-variable 'haskell-literate)
              (if (string-match "\\.lagda$" (buffer-file-name))
                  'latex))
         (setq haskell-indent-mode t)
         (run-hooks 'haskell-indent-hook))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Comments and paragraphs

(defun agda2-comments-and-paragraphs-setup nil
  "Sets up comment and paragraph handling for Agda mode."

  ;; Syntax table setup for comments is done elsewhere.

  ;; Empty lines (all white space according to Emacs) delimit
  ;; paragraphs.
  (set (make-local-variable 'paragraph-start) "\\s-*$")
  (set (make-local-variable 'paragraph-separate) paragraph-start)

  ;; Support for adding/removing comments.
  (set (make-local-variable 'comment-padding) " ")
  (set (make-local-variable 'comment-start) "--")

  ;; Support for proper filling of text in comments (requires that
  ;; Filladapt is activated).
  (when (featurep 'filladapt)
    (add-to-list (make-local-variable
                  'filladapt-token-table)
                 '("--" agda2-comment))
    (add-to-list (make-local-variable 'filladapt-token-match-table)
                 '(agda2-comment agda2-comment) t)
    (add-to-list (make-local-variable 'filladapt-token-conversion-table)
                 '(agda2-comment . exact))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Go to definition site

(defun agda2-goto-definition-keyboard (&optional other-window)
  "Go to the definition site of the name under point (if any). If this
function is invoked with a prefix argument then another window is used
to display the given position."
  (interactive "P")
  (annotation-goto-indirect (point) other-window))

(defun agda2-goto-definition-mouse (ev prefix)
  "Go to the definition site of the name clicked on, if any, and yank
otherwise (see `mouse-yank-at-click')."
  (interactive "e\nP")
  (let ((pos (posn-point (event-end ev))))
    (if (annotation-goto-possible pos)
        (annotation-goto-indirect pos)
      (mouse-yank-at-click ev prefix))))

(defun agda2-go-back nil
  "Go back to the previous position in which
`agda2-goto-definition-keyboard' or `agda2-goto-definition-mouse' was
invoked."
  (interactive)
  (annotation-go-back))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Implicit arguments

(defun agda2-display-implicit-arguments (&optional arg)
  "Toggle display of implicit arguments.
With prefix argument, turn on display of implicit arguments if
the argument is a positive number, otherwise turn it off."
  (interactive "P")
  (cond ((eq arg nil)       (agda2-go "toggleImplicitArgs"))
        ((and (numberp arg)
              (> arg 0))    (agda2-go "showImplicitArgs" "True"))
        (t                  (agda2-go "showImplicitArgs" "False"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;

(defun agda2-popup-menu-3 (ev)
  "If in a goal, popup the goal menu and call chosen command."
  (interactive "e")
  (let (choice)
    (save-excursion
      (and (agda2-goal-at (goto-char (posn-point (event-end ev))))
           (setq choice (x-popup-menu ev agda2-goal-map))
           (call-interactively
            (lookup-key agda2-goal-map (apply 'vector choice)))))))

(provide 'agda2-mode)
