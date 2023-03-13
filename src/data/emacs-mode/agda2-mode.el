;;; agda2-mode.el --- Major mode for Agda       -*- lexical-binding: t; -*-

;; Version: 2.6.3
;; Package-Requires: ((emacs "25.1") (xref "1.0.2"))
;; Keywords: languages
;; URL: https://github.com/agda/agda/tree/master/src/data/emacs-mode
;; SPDX-License-Identifier: MIT License

;;; Commentary:

;; A major mode for editing Agda (the dependently typed programming
;; language / interactive theorem prover).
;;
;; Major features include:
;;
;; - syntax highlighting.
;; - on the fly Agda interpretation.
;; - goal-driven development
;; - interactive case-splitting
;; - proof search
;; - input support (for utf8 characters)
;;
;; See https://agda.readthedocs.io/ for more information.

;;; Code:

(defvar agda2-version "2.6.4"
  "The version of the Agda mode.
Note that the same version of the Agda executable must be used.")

(require 'cl-lib)
(require 'compile)
(require 'pp)
(require 'time-date)
(require 'eri)
(require 'fontset)
(require 'agda-input)
(require 'agda2)
(require 'agda2-highlight)
(require 'agda2-abbrevs)
(require 'xref)

;; Load filladapt, if it is installed.
(require 'filladapt nil :noerror)

;;;; User options

(defgroup agda2 nil
  "Major mode for interactively developing Agda programs."
  :group 'languages)

(defcustom agda2-program-name "agda"
  "The name of the Agda executable."
  :type 'string
  :group 'agda2)

(defcustom agda2-program-args nil
  "Command-line arguments given to the Agda executable (one per string).

Note: Do not give several arguments in the same string.

The flag \"--interaction\" is always included as the first
argument, and does not need to be listed here."
  :type '(repeat string)
  :group 'agda2)

(defvar agda2-backends '("GHC" "GHCNoMain" "JS" "LaTeX" "QuickLaTeX")
  "Compilation backends.")

(defcustom agda2-backend
  ""
  "The backend used to compile Agda programs (leave blank to ask every time)."
  :type 'string
  :group 'agda2)

(defcustom agda2-information-window-max-height
  0.35
  "The maximum height of the information window.
A multiple of the frame height."
  :type 'number
  :group 'agda2)

(defcustom agda2-fontset-name
  (unless (or (eq window-system 'mac)
              ;; Emacs-23 uses a revamped font engine which should
              ;; make agda2-fontset-name unnecessary in most cases.
              ;; And if it turns out to be necessary, we should
              ;; probably use face-remapping-alist rather than
              ;; set-frame-font so the special font only applies to
              ;; Agda buffers, and so it applies in all frames where
              ;; Agda buffers are displayed.
              (boundp 'face-remapping-alist))
    "fontset-agda2")
  "Default font to use in the selected frame when activating the Agda mode.
This is only used if it's non-nil and Emacs is not running in a
terminal.

Note that this setting (if non-nil) affects non-Agda buffers as
well, and that you have to restart Emacs if you want settings to
this variable to take effect."
  :type '(choice (string :tag "Fontset name")
                 (const :tag "Do not change the font" nil))
  :group 'agda2)

(defcustom agda2-fontset-spec-of-fontset-agda2
    "-*-fixed-Medium-r-Normal-*-18-*-*-*-c-*-fontset-agda2,
    ascii:-Misc-Fixed-Medium-R-Normal--18-120-100-100-C-90-ISO8859-1,
    latin-iso8859-2:-*-Fixed-*-r-*-*-18-*-*-*-c-*-iso8859-2,
    latin-iso8859-3:-*-Fixed-*-r-*-*-18-*-*-*-c-*-iso8859-3,
    latin-iso8859-4:-*-Fixed-*-r-*-*-18-*-*-*-c-*-iso8859-4,
    cyrillic-iso8859-5:-*-Fixed-*-r-*-*-18-*-*-*-c-*-iso8859-5,
    greek-iso8859-7:-*-Fixed-*-r-*-*-18-*-*-*-c-*-iso8859-7,
    latin-iso8859-9:-*-Fixed-*-r-*-*-18-*-*-*-c-*-iso8859-9,
    mule-unicode-0100-24ff:-Misc-Fixed-Medium-R-Normal--18-120-100-100-C-90-ISO10646-1,
    mule-unicode-2500-33ff:-Misc-Fixed-Medium-R-Normal--18-120-100-100-C-90-ISO10646-1,
    mule-unicode-e000-ffff:-Misc-Fixed-Medium-R-Normal--18-120-100-100-C-90-ISO10646-1,
    japanese-jisx0208:-Misc-Fixed-Medium-R-Normal-ja-18-*-*-*-C-*-JISX0208.1990-0,
    japanese-jisx0212:-Misc-Fixed-Medium-R-Normal-ja-18-*-*-*-C-*-JISX0212.1990-0,
    thai-tis620:-Misc-Fixed-Medium-R-Normal--24-240-72-72-C-120-TIS620.2529-1,
    lao:-Misc-Fixed-Medium-R-Normal--24-240-72-72-C-120-MuleLao-1,
    tibetan:-TibMdXA-fixed-medium-r-normal--16-160-72-72-m-160-MuleTibetan-0,
    tibetan-1-column:-TibMdXA-fixed-medium-r-normal--16-160-72-72-m-80-MuleTibetan-1,
    korean-ksc5601:-Daewoo-Mincho-Medium-R-Normal--16-120-100-100-C-160-KSC5601.1987-0,
    chinese-gb2312:-ISAS-Fangsong ti-Medium-R-Normal--16-160-72-72-c-160-GB2312.1980-0,
    chinese-cns11643-1:-HKU-Fixed-Medium-R-Normal--16-160-72-72-C-160-CNS11643.1992.1-0,
    chinese-big5-1:-ETen-Fixed-Medium-R-Normal--16-150-75-75-C-160-Big5.ETen-0,
    chinese-big5-2:-ETen-Fixed-Medium-R-Normal--16-150-75-75-C-160-Big5.ETen-0"
  "Specification of the \"fontset-agda2\" fontset.
This fontset is only created if `agda2-fontset-name' is
\"fontset-agda2\" and Emacs is not run in a terminal.

Note that the text \"fontset-agda2\" has to be part of the
string (in a certain way; see the default setting) in order for the
agda2 fontset to be created properly.

Note also that the default setting may not work unless suitable
fonts are installed on your system. Refer to the README file
accompanying the Agda distribution for more details.

Note finally that you have to restart Emacs if you want settings
to this variable to take effect."
  :group 'agda2
  :type 'string)

(if (and (equal agda2-fontset-name "fontset-agda2") window-system)
    (create-fontset-from-fontset-spec agda2-fontset-spec-of-fontset-agda2 t t))

;;;; Global and buffer-local vars, initialization

(defvar agda2-mode-syntax-table
  (let ((tbl (make-syntax-table)))
    ;; Set the syntax of every char to "w" except for those whose default
    ;; syntax in `standard-syntax-table' is `paren' or `whitespace'.
    (map-char-table (lambda (keys val)
                      ;; `keys' here can be a normal char, a generic char
                      ;; (Emacs<23), or a char range (Emacs>=23).
                      (unless (memq (car val)
                                    (eval-when-compile
                                      (mapcar #'car
                                              (list (string-to-syntax "(")
                                                    (string-to-syntax ")")
                                                    (string-to-syntax " ")))))
                        (modify-syntax-entry keys "w" tbl)))
                    (standard-syntax-table))
    ;; Then override the remaining special cases.
    (dolist (cs '((?- . "w 12") (?\n . ">")
                  (?. . ".") (?\; . ".") (?! . ".")))
      (modify-syntax-entry (car cs) (cdr cs) tbl))
    tbl)
  "Syntax table used by the Agda mode:

-   | Comment character, word constituent.
\n  | Comment ender.
.;! | Punctuation.

Remaining characters inherit their syntax classes from the
standard syntax table if that table treats them as matching
parentheses or whitespace.  Otherwise they are treated as word
constituents.")

(defvar agda2-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-s") #'agda2-solve-maybe-all)
    (define-key m (kbd "C-c C-a") #'agda2-auto-maybe-all)
    (define-key m (kbd "C-c C-d") #'agda2-infer-type-maybe-toplevel)
    (define-key m (kbd "C-c C-w") #'agda2-why-in-scope-maybe-toplevel)
    (define-key m (kbd "C-c C-z") #'agda2-search-about-toplevel)
    (define-key m (kbd "C-c C-o") #'agda2-module-contents-maybe-toplevel)
    (define-key m (kbd "C-c C-n") #'agda2-compute-normalised-maybe-toplevel)
    (define-key m (kbd "S-<iso-lefttab>") #'eri-indent-reverse)
    (define-key m (kbd "S-<lefttab>")     #'eri-indent-reverse)
    (define-key m (kbd "S-<tab>")         #'eri-indent-reverse)
    (define-key m (kbd "<mouse-2>")       #'xref-find-definitions-at-mouse)
    (define-key m (kbd "C-c C-l")         #'agda2-load)
    (define-key m (kbd "C-c C-x C-c")     #'agda2-compile)
    (define-key m (kbd "C-c C-x C-q")     #'agda2-quit)
    (define-key m (kbd "C-c C-x C-r")     #'agda2-restart)
    (define-key m (kbd "C-c C-x C-a")     #'agda2-abort)
    (define-key m (kbd "C-c C-x C-d")     #'agda2-remove-annotations)
    (define-key m (kbd "C-c C-x C-h")     #'agda2-display-implicit-arguments)
    (define-key m (kbd "C-c C-x C-i")     #'agda2-display-irrelevant-arguments)
    (define-key m (kbd "C-c C-=")         #'agda2-show-constraints)
    (define-key m (kbd "C-c C-?")         #'agda2-show-goals)
    (define-key m (kbd "C-c C-f")         #'agda2-next-goal) ; Forward.
    (define-key m (kbd "C-c C-b")         #'agda2-previous-goal) ; Back.
    (define-key m (kbd "C-c C-x M-;")     #'agda2-comment-dwim-rest-of-buffer)
    (define-key m (kbd "C-c C-x C-s")     #'agda2-set-program-version)
    (define-key m (kbd "<down-mouse-3>") #'agda2-popup-menu-3)
    (define-key m (kbd "C-c C-SPC")       #'agda2-give)
    (define-key m (kbd "C-c SPC")         #'agda2-give)
    (define-key m (kbd "C-c C-m")         #'agda2-elaborate-give)
    (define-key m (kbd "C-c C-r")         #'agda2-refine)
    (define-key m (kbd "C-c C-c")         #'agda2-make-case)
    (define-key m (kbd "C-c C-t")         #'agda2-goal-type)
    (define-key m (kbd "C-c C-e")         #'agda2-show-context)
    (define-key m (kbd "C-c C-h")         #'agda2-helper-function-type)
    (define-key m (kbd "C-c C-,")         #'agda2-goal-and-context)
    (define-key m (kbd "C-c C-.")         #'agda2-goal-and-context-and-inferred)
    (define-key m (kbd "C-c C-;")         #'agda2-goal-and-context-and-checked)
    m)
  "Bindings for `agda2-mode'.")

(defvar agda2-repeat-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-f")   #'agda2-next-goal)
    (define-key m (kbd "C-b")   #'agda2-previous-goal)
    (define-key m (kbd "C-SPC") #'agda2-give)
    (define-key m (kbd "C-r")   #'agda2-refine)
    (define-key m (kbd "C-c")   #'agda2-make-case)
    (define-key m (kbd "C-,")   #'agda2-goal-and-context)
    (define-key m (kbd "C-.")   #'agda2-goal-and-context-and-inferred)
    (define-key m (kbd "C-;")   #'agda2-goal-and-context-and-checked)
    m)
  "Agda bindings to repeat in conjunction with `repeat-mode'.")

(dolist (command '(agda2-next-goal
                   agda2-previous-goal
                   agda2-give
                   agda2-refine
                   agda2-make-case
                   agda2-goal-and-context
                   agda2-goal-and-context-and-inferred
                   agda2-goal-and-context-and-checked))
  (put command 'repeat-map 'agda2-movement-repeat-map))

(defvar agda2-common-menu-items
  '(["Solve constraints" agda2-solve-maybe-all]
    ["Auto" agda2-auto-maybe-all]
    ["Infer (deduce) type" agda2-infer-type-maybe-toplevel]
    ["Explain why a particular name is in scope" agda2-why-in-scope-maybe-toplevel]
    ["Search About" agda2-search-about-toplevel]
    ["Module contents" agda2-module-contents-maybe-toplevel]
    ["Evaluate term to normal form" agda2-compute-normalised-maybe-toplevel])
  "Menu items between `agda2-mode-menu' and `agda2-goal-menu'.")

(easy-menu-define agda2-mode-menu agda2-mode-map
  "Menu for Agda mode."
  `(Agda
    ,@agda2-common-menu-items
    ["Load" agda2-load]
    ["Compile" agda2-compile]
    ["Quit" agda2-quit]
    ["Kill and restart Agda" agda2-restart]
    ["Abort a command" agda2-abort]
    ["Remove goals and highlighting (\"deactivate\")" agda2-remove-annotations]
    ["Toggle display of hidden arguments" agda2-display-implicit-arguments]
    ["Toggle display of irrelevant arguments" agda2-display-irrelevant-arguments]
    ["Show constraints" agda2-show-constraints]
    ["Show goals" agda2-show-goals]
    ["Next goal" agda2-next-goal] ; Forward.
    ["Previous goal" agda2-previous-goal] ; Back.
    ["Information about the character at point" describe-char]
    ["Comment/uncomment the rest of the buffer" agda2-comment-dwim-rest-of-buffer]
    ["Version" agda2-display-program-version]
    ["Switch to another version of Agda" agda2-set-program-version]))

(easy-menu-define agda2-goal-menu agda2-mode-map
  "Menu for Agda mode."
  `(Agda
    ,@agda2-common-menu-items
    ["Give" agda2-give]
    ["Elaborate and Give" agda2-elaborate-give]
    ["Refine" agda2-refine]
    ["Case" agda2-make-case]
    ["Goal type" agda2-goal-type]
    ["Context (environment)" agda2-show-context]
    ["Helper function type" agda2-helper-function-type]
    ["Goal type and context" agda2-goal-and-context]
    ["Goal type, context and inferred type" agda2-goal-and-context-and-inferred]
    ["Goal type, context and checked type" agda2-goal-and-context-and-checked]))

(defvar agda2-info-buffer nil
  "Agda information buffer.")

(defvar agda2-process-buffer nil
  "Agda subprocess buffer.
Set in `agda2-restart'.")

(defvar agda2-process nil
  "Agda subprocess.
Set in `agda2-restart'.")

(defvar agda2-in-progress nil
  "Is the Agda process currently busy?
Valid values: nil (not busy), `busy' (busy),
`not-so-busy' (busy with something that should typically
terminate fairly quickly).")

;; Some buffer locals
(defvar-local agda2-buffer-external-status ""
  "External status of an `agda2-mode' buffer (dictated by the Haskell side).")

(defvar agda2-output-prompt "Agda2> "
  "The Agda2 buffer's prompt.")

(defconst agda2-help-address
  ""
  "Address accepting submissions of bug reports and questions.")

;; Annotation for a goal
;; {! .... !}
;; ----------  overlay:    agda2-gn num, face highlight, after-string num,
;;                         modification-hooks (agda2-protect-goal-markers)
;; -           text-props: category agda2-delim1
;;  -          text-props: category agda2-delim2
;;         -   text-props: category agda2-delim3
;;          -  text-props: category agda2-delim4
;;
;; Char categories for {! ... !}
(defvar agda2-open-brace  "{")
(defvar agda2-close-brace " }")
(setplist 'agda2-delim1 `(display ,agda2-open-brace))
(setplist 'agda2-delim2 `(display ,agda2-open-brace rear-nonsticky t
                                  agda2-delim2 t))
(setplist 'agda2-delim3 `(display ,agda2-close-brace agda2-delim3 t))
(setplist 'agda2-delim4 `(display ,agda2-close-brace rear-nonsticky t))

;; Note that strings used with the display property are compared by
;; reference. If the agda2-*-brace definitions were inlined, then
;; goals would be displayed as "{{ }}n" instead of "{ }n".

;; The following variables are used by the filter process,
;; `agda2-output-filter'. Their values are only modified by the filter
;; process, `agda2-go', `agda2-restart', `agda2-abort-highlighting',
;; and `agda2-abort-done'.

(defvar agda2-output-chunk-incomplete (get-buffer-create " *Agda2 Incomplete Output*")
  "Buffer for incomplete lines.
\(See `agda2-output-filter'.)")

(defvar-local agda2-last-responses nil
  "Response commands which should be run after other commands.
The command which arrived last is stored first in the list.")

(defvar agda2-file-buffer nil
  "The Agda buffer.
Note that this variable is not buffer-local.")

(defvar agda2-in-agda2-file-buffer nil
  "Was `agda2-file-buffer' active when `agda2-output-filter' started?
Note that this variable is not buffer-local.")

;;;; `agda2-mode' Definition

;;;###autoload
(define-derived-mode agda2-mode prog-mode "Agda"
  "Major mode for Agda files.

\\{agda2-mode-map}"

 (if (boundp 'agda2-include-dirs)
     (display-warning 'agda2 "Note that the variable agda2-include-dirs is
no longer used. You may want to update your configuration. You
have at least two choices:
* Use the library management system.
* Set the include path using agda2-program-args.

One way to avoid seeing this warning is to make sure that
agda2-include-dirs is not bound." :warning))

 (setq local-abbrev-table agda2-mode-abbrev-table
       indent-tabs-mode   nil
       mode-line-process
         '((:eval (unless (eq 0 (length agda2-buffer-external-status))
                    (concat ":" agda2-buffer-external-status)))))
 (let ((l '(max-specpdl-size    2600
            max-lisp-eval-depth 2800)))
   (while l (set (make-local-variable (pop l)) (pop l))))
 (if (and window-system agda2-fontset-name)
     (condition-case nil
         (set-frame-font agda2-fontset-name)
       (error (error "Unable to change the font; change agda2-fontset-name or tweak agda2-fontset-spec-of-fontset-agda2"))))
 ;; Deactivate highlighting if the buffer is edited before
 ;; typechecking is complete.
 (add-hook 'first-change-hook #'agda2-abort-highlighting nil 'local)
 ;; If Agda is not running syntax highlighting does not work properly.
 (unless (eq 'run (agda2-process-status))
   (ignore-errors (agda2-restart)))
 ;; Make sure that Font Lock mode is not used.
 (font-lock-mode 0)
 (agda2-highlight-setup)
 (condition-case err
     (agda2-highlight-reload)
   (error (message "Highlighting not loaded: %s"
                   (error-message-string err))))
 (agda2-comments-and-paragraphs-setup)
 (force-mode-line-update)
 ;; Protect global value of default-input-method from set-input-method.
 (make-local-variable 'default-input-method)
 ;; Don't take script into account when determining word boundaries
 (setq-local word-combining-categories (cons '(nil . nil) word-combining-categories))
 (activate-input-method "Agda")
 ;; Highlighting etc. is removed when we switch from the Agda mode.
 ;; Use case: When a file M.lagda with a local variables list
 ;; including "mode: latex" is loaded chances are that the Agda mode
 ;; is activated before the LaTeX mode, and the LaTeX mode does not
 ;; seem to remove the text properties set by the Agda mode.
 (add-hook 'change-major-mode-hook #'agda2-quit nil 'local)
 ;; Enable Xref
 (add-hook 'xref-backend-functions #'agda2-xref-backend -90 t)
 ;; Use ERI for indentation
 (setq indent-line-function #'eri-indent))

(defun agda2-restart ()
  "Try to start or restart the Agda process."
  (interactive)

  ;; Kill any running instance of the Agda process.
  (condition-case nil
      (agda2-term)
    (error nil))

  ;; Check that the right version of Agda is used.
  (let* ((coding-system-for-read 'utf-8)
         (output (with-output-to-string
                   (call-process agda2-program-name
                                 nil standard-output nil "--version")))
         (version (and (string-match "^Agda version \\([0-9.]+\\)" output)
                       (match-string 1 output))))
    (unless (equal version agda2-version)
      (error "The Agda mode's version (%s) does not match that of %s (%s)"
             agda2-version
             agda2-program-name (or version "unknown"))))

  (let ((all-program-args (cons "--interaction" agda2-program-args)))

    ;; Check that the arguments are not malformed.
    (let* ((coding-system-for-read 'utf-8)
           (status)
           (output
            (with-output-to-string
              (setq status
                    (apply #'call-process agda2-program-name
                           nil standard-output nil all-program-args)))))
      (unless (zerop status)
        (error "Failed to start the Agda process:\n%s" output)))

    ;; Start the Agda process.
    (let ((agda2-bufname " *agda2*"))

      (let ((process-connection-type nil)) ; Pipes are faster than PTYs.
        (setq agda2-process
              (apply #'start-process "Agda2" agda2-bufname
                     agda2-program-name all-program-args)))

      (set-process-coding-system agda2-process 'utf-8 'utf-8)
      (set-process-query-on-exit-flag agda2-process nil)
      (set-process-filter agda2-process #'agda2-output-filter)
      (setq agda2-in-progress nil
            agda2-file-buffer (current-buffer))

      (with-current-buffer agda2-bufname
        (setq agda2-process-buffer (current-buffer)
              mode-name            "Agda executable"
              agda2-last-responses nil)
        (set-buffer-file-coding-system 'utf-8))

      (agda2-remove-annotations))))

;;;; Communicating with Agda

(defun agda2-raise-error ()
  "Raise an error.
The error message directs the user to the *agda2* buffer."
  (error "Problem encountered, the *agda2* buffer can perhaps explain why"))

(defun agda2-running-p nil
  "Does the *agda2* buffer exist, and is the Agda2 process running?"
  (and (buffer-live-p agda2-process-buffer)
       (eq (agda2-process-status) 'run)))

(defun agda2-send-command (restart &rest args)
  "Send a command to the Agda process.
Sends the list of strings ARGS to the process.  If RESTART is
non-nil and the process is not running, or the *agda2*
buffer does not exist, then an attempt is made to restart the
process."
  (when (and restart (not (agda2-running-p)))
    ;; Try restarting automatically, but only once, in case there is
    ;; some major problem.
    (agda2-restart)
    (unless (agda2-running-p)
      (agda2-raise-error)))
  (with-current-buffer agda2-process-buffer
    (goto-char (point-max))
    (let ((point (point)))
      (insert (mapconcat #'identity args " ") "\n")
      (process-send-region agda2-process point (point-max)))))

(defun agda2-go (save highlight how-busy do-abort &rest args)
  "Execute commands in the Agda2 interpreter.
Sends the list of strings ARGS to the Agda2 interpreter, waits
for output and executes the responses, if any.

If SAVE is \\='save, then the buffer is saved first.

If HIGHLIGHT is non-nil, then the buffer's syntax highlighting
may be updated.  This is also the case if the Agda process is
busy (or `not-so-busy') and `agda2-highlight-in-process' is
non-nil.

The value HOW-BUSY should be `busy' if it should not be possible
to invoke other commands while this command is running (with the
exception of commands for which DO-ABORT is nil).  Otherwise it
should be `not-so-busy' (which should only be used for commands
that typically terminate fairly quickly).

If the Agda process is busy (or `not-so-busy'), and the current
buffer does not match `agda2-file-buffer', then the command is
not executed and an error is raised.  The same applies if DO-ABORT
is non-nil and the Agda process is `busy'."

  ; Check that how-busy is well-formed.
  (cl-assert (memq how-busy '(busy not-so-busy)))

  (when (and agda2-in-progress
             (not (eq agda2-file-buffer (current-buffer))))
    (error "Agda is busy with something in the buffer %s"
           agda2-file-buffer))

  (when (and do-abort
             (eq agda2-in-progress 'busy))
    (error "Agda is busy with something \
\(you have the option to abort or restart Agda)"))

  (setq agda2-file-buffer (current-buffer))

  (setq agda2-highlight-in-progress
        (or highlight
            (and agda2-in-progress
                 agda2-highlight-in-progress)))

  (setq agda2-in-progress
        (if (or (eq how-busy 'busy)
                (eq agda2-in-progress 'busy))
            'busy
          'not-so-busy))

  (when (eq save 'save) (save-buffer))

  (apply #'agda2-send-command
         'restart
         "IOTCM"
         (agda2-string-quote (buffer-file-name))
         (if highlight (agda2-highlight-level) "None")
         "Indirect"
         "("
         (append args '(")"))))

(defun agda2-abort ()
  "Try to abort the current computation, if any.
May be more efficient than restarting Agda."
  (interactive)
  (agda2-send-command nil
                      "IOTCM"
                      (agda2-string-quote (buffer-file-name))
                      "None"
                      "Indirect"
                      "Cmd_abort"))

(defun agda2-output-filter (_proc chunk)
  "Evaluate the Agda partial output CHUNK.
This filter function assumes that every line contains either some
kind of error message (which cannot be parsed as a list), or
exactly one command.  Incomplete lines are stored in a
buffer (`agda2-output-chunk-incomplete').

Every command is run by this function, unless it has the form
\"(('last . priority) . cmd)\", in which case it is run by
`agda2-run-last-commands' at the end, after the Agda2 prompt
has reappeared, after all non-last commands, and after all
interactive highlighting is complete.  The last commands can have
different integer priorities; those with the lowest priority are
executed first.

Non-last commands should not call the Agda process.

All commands are echoed to the *agda2* buffer, with the exception
of commands of the form \"(agda2-highlight-... ...)\".

The non-last commands are run in the order in which they appear.

When the prompt has been reached highlighting annotations are
reloaded from `agda2-highlighting-file', unless
`agda2-highlighting-in-progress' is nil."
  ;; Beware: the buffer may have been killed in the mean time.  E.g. when
  ;; viewing an attachment containing Agda code in Gnus, Gnus will
  ;; create a temp buffer, set it in agda2-mode, call font-lock-ensure on it
  ;; (which won't know that it needs to wait for some process to reply), then
  ;; extract the fontified text and kill the temp buffer; so when Agda
  ;; finally answers, the temp buffer is long gone.
  (when (buffer-live-p agda2-file-buffer)
    (setq agda2-in-agda2-file-buffer
          (and agda2-file-buffer
               (eq (current-buffer) agda2-file-buffer)))
    (let (;; The input lines in the current chunk.
          (lines (split-string chunk "\n"))

          ;; Non-last commands found in the current chunk (reversed).
          (non-last-commands ())

          ;; Last incomplete line, if any.
          (output-chunk-incomplete ""))
      (with-current-buffer agda2-file-buffer
        (when (consp lines)
          (with-current-buffer agda2-output-chunk-incomplete
            (goto-char (point-max))
            (insert (pop lines)))
          (when (consp lines)
            ;; The previous uncomplete chunk is now complete.
            (push (with-current-buffer agda2-output-chunk-incomplete
                    (prog1 (buffer-string)
                      (erase-buffer)
                      ;; Stash away the last incomplete line, if any. (Note that
                      ;; (split-string "...\n" "\n") evaluates to (... "").)
                      (setq output-chunk-incomplete (car (last lines)))
                      (insert output-chunk-incomplete)))
                  lines))))

      ;; Handle every complete line.
      (dolist (line (butlast lines))
        (let* (;; The command. Lines which cannot be parsed as a single
               ;; list, without any junk, are ignored.
               (cmd (condition-case nil
                        (let ((result (read-from-string line)))
                          (if (and (listp (car result))
                                   (= (cdr result) (length line)))
                              (car result)))
                      (error nil)))
               (is-highlighting-command
                (and cmd
                     (symbolp (car cmd))
                     (let ((case-fold-search nil))
                       (string-match "^agda2-highlight-"
                                     (symbol-name (car cmd)))))))

          ;; Do not echo highlighting commands.
          (unless is-highlighting-command
            (with-current-buffer agda2-process-buffer
              (save-excursion
                (goto-char (point-max))
                (insert line)
                (insert "\n"))))
          (when cmd
            (if (eq 'last (car-safe (car cmd)))
                (push (cons (cdr (car cmd)) (cdr cmd))
                      agda2-last-responses)
              (push cmd non-last-commands)))))

      ;; Run non-last commands.
      (mapc #'agda2-exec-response (nreverse non-last-commands))

      ;; Check if the prompt has been reached. This function assumes
    ;; that the prompt does not include any newline characters.
    (when (with-current-buffer agda2-output-chunk-incomplete
            (search-backward-regexp (concat "\\`" agda2-output-prompt) nil t))
      (with-current-buffer agda2-process-buffer
        (insert output-chunk-incomplete))
      (with-current-buffer agda2-output-chunk-incomplete
        (erase-buffer))
      (setq agda2-in-progress nil
            agda2-last-responses (nreverse agda2-last-responses))

      (agda2-run-last-commands)))))

(defun agda2-run-last-commands nil
  "Execute the last commands in the right order.
\(After the prompt has reappeared.) See `agda2-output-filter'."

  ;; with-current-buffer is used repeatedly below, because some last
  ;; commands may switch the focus to another buffer.

  (while (with-current-buffer agda2-file-buffer
           (and (not agda2-in-progress) (consp agda2-last-responses)))
    (with-current-buffer agda2-file-buffer
      ;; The list is sorted repeatedly because this function may be
      ;; called recursively (via `agda2-exec-response').
      (setq agda2-last-responses (sort agda2-last-responses
                                       (lambda (x y) (<= (car x) (car y)))))
      (let ((r (pop agda2-last-responses)))
        (agda2-exec-response (cdr r)))))

  ;; Unset agda2-highlight-in-progress when all the asynchronous
  ;; commands have terminated.
  (unless agda2-in-progress
      (setq agda2-highlight-in-progress nil)))

(defun agda2-abort-highlighting nil
  "Abort any interactive highlighting.
This function should be used in `first-change-hook'."
  (when agda2-highlight-in-progress
    (setq agda2-highlight-in-progress nil)
    (message "\"%s\" has been modified. Interrupting highlighting."
             (buffer-name (current-buffer)))))

(defun agda2-goal-cmd (cmd save &optional want ask &rest args)
  "Read input from goal or minibuffer and sends command to Agda.

An error is raised if point is not in a goal.

The command sent to Agda is

  CMD <goal number> <goal range> <user input> ARGS.

The user input is computed as follows:

* If WANT is nil, then the user input is the empty string.

* If WANT is a string, and either ASK is non-nil or the goal only
  contains whitespace, then the input is taken from the
  minibuffer.  In this case WANT is used as the prompt string.

* Otherwise (including if WANT is \\='goal) the goal contents are
  used.

If the user input is not taken from the goal, then an empty goal
range is given.

If SAVE is \\='save, then the buffer is saved just before the
command is sent to Agda (if it is sent)."
  (cl-multiple-value-bind (o g) (agda2-goal-at (point))
    (unless g (error "For this command, please place the cursor in a goal"))
    (let ((txt (buffer-substring-no-properties (+ (overlay-start o) 2)
                                               (- (overlay-end   o) 2)))
          (input-from-goal nil))
      (cond ((null want) (setq txt ""))
            ((and (stringp want)
                  (or ask (string-match "\\`\\s *\\'" txt)))
             (setq txt (read-string (concat want ": ") nil nil txt t)))
            (t (setq input-from-goal t)))
      (apply #'agda2-go save input-from-goal 'busy t cmd
             (format "%d" g)
             (if input-from-goal (agda2-goal-Range o) (agda2-mkRange nil))
             (agda2-string-quote txt) args))))

(defun agda2-exec-response (response)
  "Execute RESPONSE if recognised by `agda2-handler-alist'."
  (cl-assert (symbolp (car-safe response)))
  ;; We check the symbol property `agda2-safe-function' for the
  ;; function being called, instead of just calling `eval'.  This is
  ;; done to avoid the possible security risks of evaluating foreign
  ;; code.  The arguments are likewise not evaluated, just unquoted
  ;; and checked if they satisfy the expected types.
  (let* ((inhibit-read-only t)
         (func (car response))
         (safe-p (plist-member (symbol-plist func) 'agda2-safe-function))
         (safe-data (get func 'agda2-safe-function))
         args)
    (unless safe-p
      (error "The function `%S' is not a valid Agda command" func))
    ;; Check each argument
    (dolist (arg (cdr response))
      (when (null safe-data)
        (error "More arguments than expected"))
      (when (eq (car-safe arg) 'quote) ;unquote arguments
        (setq arg(cadr arg)))
      (let ((type (pop safe-data)))
        (unless (cl-typep arg type)
          (error "The function `%S' was invoked with %S which is not a %S"
                 func arg type)))
      (push arg args))
    (apply func (nreverse args))))

(defun agda2-abort-done ()
  "Reset certain variables.
Intended to be used by the backend if an abort command was
successful."
  (declare (agda2-command))
  (agda2-info-action "*Aborted*" "Aborted." t)
  (setq agda2-highlight-in-progress nil
        agda2-last-responses        nil))

;;;; User commands and response processing

(defun agda2-load ()
  "Load current buffer."
  (interactive)
  (agda2-go 'save t 'busy t "Cmd_load"
            (agda2-string-quote (buffer-file-name))
            (agda2-list-quote agda2-program-args)))

(defun agda2-compile ()
  "Compile the current module.

The variable `agda2-backend' determines which backend is used."
  (interactive)
  (let ((backend (cond ((equal agda2-backend "MAlonzo")       "GHC")
                       ((equal agda2-backend "MAlonzoNoMain") "GHCNoMain")
                       ((equal agda2-backend "")
                        (completing-read "Backend: " agda2-backends
                                         nil nil nil nil nil
                                         'inherit-input-method))
                       (t agda2-backend))))
    (when (equal backend "") (error "No backend chosen"))
    (agda2-go 'save t 'busy t "Cmd_compile"
              backend
              (agda2-string-quote (buffer-file-name))
              (agda2-list-quote agda2-program-args))))

(defmacro agda2-maybe-forced (name comment cmd save want)
  "Construct a function NAME to run CMD.
COMMENT is used to build the function's comment.  The function
NAME takes a prefix argument which tells whether it should
apply force or not when running CMD (through
`agda2-goal-cmd';
SAVE is used as `agda2-goal-cmd's SAVE argument and
WANT is used as `agda2-goal-cmd's WANT argument)."
  (let ((eval (make-symbol "eval")))
  `(defun ,name (&optional prefix)
     ,(concat comment ".

The action depends on the prefix argument:

* If the prefix argument is `nil' (i.e., if no prefix argument is
  given), then no force is applied.

* If any other prefix argument is used (for instance, if C-u is
  typed once or twice right before the command is invoked), then
  force is applied.")
     (interactive "P")
     (let ((,eval (cond ((null prefix) "WithoutForce")
                        ("WithForce"))))
       (agda2-goal-cmd (concat ,cmd " " ,eval)
                       ,save ,want)))))

(agda2-maybe-forced
  agda2-give
  "Give to the goal at point the expression in it"
  "Cmd_give"
  'save
  "expression to give")

;; (defun agda2-give()
;;   "Give to the goal at point the expression in it" (interactive)
;;   (agda2-goal-cmd "Cmd_give" 'save "expression to give"))

(defun agda2-give-action (old-g paren)
  "Update the goal OLD-G with the expression in it.
See `agda2-update' for details on PAREN."
  (declare (agda2-command integer (or (eql paren)
                                  (eql no-paren)
                                  string
                                  null)))
  (let
      ;; Don't run modification hooks: we don't want this to
      ;; trigger agda2-abort-highlighting.
      ((inhibit-modification-hooks t))
    (agda2-update old-g paren)))

(defun agda2-refine (pmlambda)
  "Refine the goal at point.
If the goal contains an expression e, and some \"suffix\" of the
type of e unifies with the goal type, then the goal is replaced
by e applied to a suitable number of new goals.

PMLAMBDA is only used if the goal has a functional type.
When the prefix argument is given a pattern maching lambda will
be inserted, otherwise a standard lambda will be used.

If the goal is empty, the goal type is a data type, and there is
exactly one constructor which unifies with this type, then the
goal is replaced by the constructor applied to a suitable number
of new goals."
  (interactive "P")
  (if pmlambda
      (agda2-goal-cmd "Cmd_refine_or_intro True" 'save 'goal)
    (agda2-goal-cmd "Cmd_refine_or_intro False" 'save 'goal)))

(defun agda2-autoOne ()
  "Simple proof search."
  (interactive)
 (agda2-goal-cmd "Cmd_autoOne" 'save 'goal))

(defun agda2-autoAll ()
  "Solves all goals by simple proof search."
  (interactive)
  (agda2-go nil nil 'busy t "Cmd_autoAll"))

(defun agda2-make-case ()
  "Refine the pattern variables given in the goal.
Assumes that <clause> = {!<variables>!} is on one line."
  (interactive)
  (agda2-goal-cmd "Cmd_make_case" 'save "pattern variables to case (empty for split on result)"))

(defun agda2-make-case-action (newcls)
  "Replace the line at point with new clauses NEWCLS and reload."
  (declare (agda2-command list))
  (agda2-forget-all-goals);; we reload later anyway.
  (let* ((p0 (point))
         (p1 (goto-char (+ (current-indentation) (line-beginning-position))))
         (indent (current-column))
         cl)
    (delete-region p1 (line-end-position))
    (while (setq cl (pop newcls))
      (insert cl)
      (if newcls (insert "\n" (make-string indent ? ))))
    (goto-char p0))
  (agda2-load))

(defun agda2-make-case-action-extendlam (newcls)
  "Replace definition of extended lambda with new clauses NEWCLS and reload."
  (declare (agda2-command list))
  (agda2-forget-all-goals);; we reload later anyway.
  (let* ((p0 (point))
         (pmax (re-search-forward "!}"))
         (bracketCount 0)
         (p1 (goto-char (+ (current-indentation) (line-beginning-position))))
         (indent (current-column))
         cl)
    (goto-char p0)
    (re-search-backward "{!")
    (while (and (not (eq (preceding-char) ?\;)) (>= bracketCount 0) (> (point) p1))
      (backward-char)
      (if (eq (preceding-char) ?}) (cl-incf bracketCount))
      (if (eq (preceding-char) ?{) (cl-decf bracketCount)))
    (let* ((is-lambda-where (= (point) p1))
           (p (point)))
      (delete-region (point) pmax)
      (if (not is-lambda-where) (insert " "))
      (while (setq cl (pop newcls))
        (insert cl)
        (if newcls (if is-lambda-where (insert "\n" (make-string indent ? )) (insert " ; "))))
      (goto-char p)))
  (agda2-load))

(defun agda2-status-action (status)
  "Display the string STATUS in the current buffer's mode line.
\(precondition: the current buffer has to use the Agda mode as the
major mode)."
  (declare (agda2-command string))
  (setq agda2-buffer-external-status status)
  (force-mode-line-update))

(defmacro agda2-information-buffer (buffer kind title)
  "Define a function BUFFER that will create a KIND of buffer.
TITLE will be used for the title of the buffer if it doesn't
already exists."
  `(defun ,buffer nil
     ,(concat "Creates the Agda " kind
              " buffer, if it does not already exist.
The buffer is returned.")
  (unless (buffer-live-p ,buffer)
    (setq ,buffer
          (generate-new-buffer ,title))

    (with-current-buffer ,buffer
      (compilation-mode "AgdaInfo")
      ;; Support for jumping to positions mentioned in the text.
      (setq-local compilation-error-regexp-alist
                  '(("\\([\\\\/][^[:space:]]*\\):\\([0-9]+\\),\\([0-9]+\\)-\\(\\([0-9]+\\),\\)?\\([0-9]+\\)"
                     1 (2 . 5) (3 . 6))))
      ;; Do not skip errors that start in the same position as the
      ;; current one.
      (setq-local compilation-skip-to-next-location nil)
      ;; No support for recompilation. The key binding is removed, and
      ;; attempts to run `recompile' will (hopefully) result in an
      ;; error.
      (let ((map (copy-keymap (current-local-map))))
        (define-key map (kbd "g") 'undefined)
        (use-local-map map))
      (setq-local compile-command
                  'agda2-does-not-support-compilation-via-the-compilation-mode)

      (set-syntax-table agda2-mode-syntax-table)
      (setq-local word-combining-categories (cons '(nil . nil) word-combining-categories))
      (set-input-method "Agda")))

  ,buffer))

(agda2-information-buffer agda2-info-buffer "info" "*Agda information*")

(defun agda2-info-action (name text &optional append)
  "Insert TEXT into the Agda info buffer and display it.
NAME is displayed in the buffer's mode line.

If APPEND is non-nil, then TEXT is appended at the end of the
buffer, and point placed after this text.

If APPEND is nil, then any previous text is removed before TEXT
is inserted, and point is placed before this text."
  (declare (agda2-command string string boolean))
  (interactive)
  (let ((buf (agda2-info-buffer)))
    (with-current-buffer buf
      ;; In some cases the jump-to-position-mentioned-in-text
      ;; functionality (see compilation-error-regexp-alist above)
      ;; didn't work: Emacs jumped to the wrong position. However, it
      ;; seems to work if compilation-forget-errors is used. This
      ;; problem may be related to Emacs bug #9679
      ;; (http://debbugs.gnu.org/cgi/bugreport.cgi?bug=9679). The idea
      ;; to use compilation-forget-errors comes from a comment due to
      ;; Oleksandr Manzyuk
      ;; (https://github.com/haskell/haskell-mode/issues/67).
      (compilation-forget-errors)
      (unless append (erase-buffer))
      (save-excursion
        (goto-char (point-max))
        (insert text))
      (put-text-property 0 (length name) 'face '(:weight bold) name)
      (setq mode-line-buffer-identification name)
      (force-mode-line-update))
    ;; If the current window displays the information buffer, then the
    ;; window configuration is left untouched.
    (unless (eq (window-buffer) buf)
      (let ((agda-window
              (and agda2-file-buffer
                   (car-safe
                     ;; All windows, including minibuffers, on any
                     ;; frame on the current terminal, displaying the
                     ;; present Agda file buffer.
                     (get-buffer-window-list agda2-file-buffer t 0)))))
        (save-selected-window
          ;; Select a window displaying the Agda file buffer (if such
          ;; a window exists). With certain configurations of
          ;; display-buffer this should increase the likelihood that
          ;; the info buffer will be displayed on the same frame.
          (when agda-window
            (select-window agda-window 'no-record))
          (let* (;; If there is only one window, then the info window
                 ;; should be created above or below the code window,
                 ;; not to the left or right.
                 (split-width-threshold nil)
                 (window
                   (display-buffer
                     buf
                     ;; Under Emacs 23 the effect of the following
                     ;; argument is only that the current window
                     ;; should not be used.
                     '(nil
                       .
                       (;; Do not use the same window.
                        (inhibit-same-window . t)
                        ;; Do not raise or select another frame.
                        (inhibit-switch-frame . t))))))
            (if window
                (fit-window-to-buffer window
                  (truncate
                    (* (frame-height)
                       agda2-information-window-max-height))))))))
    ;; Move point in every window displaying the information buffer.
    ;; Exception: If we are appending, don't move point in selected
    ;; windows.
    (dolist (window (get-buffer-window-list buf 'no-minibuffer t))
      (unless (and append
                   (eq window (selected-window)))
        (with-selected-window window
          (if append
              (goto-char (point-max))
            (goto-char (point-min))))))))

(defun agda2-info-action-and-copy (name text &optional append)
  "Add TEXT to kill ring before invoking `agda2-info-action'.
For NAME, TEXT and APPEND see `agda2-info-action'."
  (declare (agda2-command string string t))
  (kill-new text)
  (agda2-info-action name text append))

(defun agda2-show-constraints ()
  "Show constraints."
  (interactive)
  (agda2-go nil t 'busy t "Cmd_constraints"))

(defun agda2-remove-annotations ()
  "Remove buffer annotations (overlays and text properties)."
  (interactive)
  (dolist (o (overlays-in (point-min) (point-max)))
    (delete-overlay o))
  (let ((inhibit-read-only t))
    (with-silent-modifications
      (set-text-properties (point-min) (point-max) '()))
    (force-mode-line-update)))

(defun agda2-next-goal ()     "Go to the next goal, if any."     (interactive)
  (agda2-mv-goal 'next-single-property-change     'agda2-delim2 1 (point-min)))
(defun agda2-previous-goal () "Go to the previous goal, if any." (interactive)
  (agda2-mv-goal 'previous-single-property-change 'agda2-delim3 0 (point-max)))
(defun agda2-mv-goal (change delim adjust wrapped)
  "Move in the direction of a goal.
CHANGE is a function like `next-single-property-change' or
`previous-single-property-change'.  DELIM is a text property
symbol that indicates what to look for.  ADJUST is the number of
characters that the search will be off by.  WRAPPED is a boundary
up until which the search will look."
  (cl-flet ((go (p) (while (and (setq p (funcall change p 'category))
                                (not (eq (get-text-property p 'category) delim))))
              (if p (goto-char (+ adjust p)))))
    (or (go (point)) (go wrapped) (message "No goals in the buffer"))))

(defun agda2-quit ()
  "Quit and clean up after agda2."
  (interactive)
  (remove-hook 'first-change-hook #'agda2-abort-highlighting 'local)
  (remove-hook 'after-save-hook #'agda2-highlight-tokens 'local)
  (agda2-remove-annotations)
  (agda2-term))

(defun agda2-term (&optional nicely)
  "Interrupt the Agda process and kill its buffer.
If this function is invoked with a prefix argument or NICELY is
non-nil, then Agda is asked nicely to terminate itself after any
previously invoked commands have completed."
  (interactive "P")
  (if nicely
      (progn
        ;; Set up things so that if the Agda process terminates, then
        ;; its buffer is killed.
        (when (and agda2-process
                   (process-status agda2-process))
          (set-process-sentinel agda2-process #'agda2-kill-process-buffer))
        ;; Kill the process buffer if the Agda process has already
        ;; been killed.
        (agda2-kill-process-buffer)
        ;; Try to kill the Agda process.
        (agda2-send-command nil
                            "IOTCM"
                            (agda2-string-quote (buffer-file-name))
                            "None"
                            "Indirect"
                            "Cmd_exit"))
    ;; Try to kill the Agda process and the process buffer.
    (when (and agda2-process
               (process-status agda2-process))
      (interrupt-process agda2-process))
    (when (buffer-live-p agda2-process-buffer)
      (kill-buffer agda2-process-buffer))))

(defun agda2-kill-process-buffer (&optional _process _event)
  "Kill the Agda process buffer, if any.
But only if the Agda process does not exist or has terminated.

This function can be used as a process sentinel."
  (when (and (or (null agda2-process)
                 (member (process-status agda2-process)
                         '(exit signal failed nil)))
             (buffer-live-p agda2-process-buffer))
    (kill-buffer agda2-process-buffer)))

(cl-defmacro agda2--with-gensyms ((&rest names) &body body)
  "Bind NAMES to fresh symbols in BODY."
  (declare (indent 1))
  `(let ,(cl-loop for x in names collecting `(,x (make-symbol (symbol-name',x))))
     ,@body))

;; This macro is meant to be used to generate other macros which define
;; functions which can be used either directly from a goal or at a global
;; level and are modifiable using one of three levels of normalisation.

(defmacro agda2-proto-maybe-normalised (name comment cmd norm0 norm1 norm2 norm3 spec)
  "Construct a function NAME that will run CMD.
COMMENT is used to build the function's comment.
The function NAME takes a prefix argument which tells whether it
should normalise types according to either NORM0, NORM1, NORM2, or NORM3
when running CMD through `agda2-goal-cmd`.
SPEC can be either (fromgoal want) or (global prompt)."
  ;; Names bound in a macro should be ``uninterned'' to avoid name capture
  ;; We use the macro `agda2--with-gensyms' to bind these.
  (agda2--with-gensyms (eval prefix args)
    `(defun ,name (,prefix &rest ,args)
       ,(format "%s.

The form of the result depends on the prefix argument:

* If the prefix argument is `nil' (i.e., if no prefix argument is
  given), then the result is %s.

* If the prefix argument is `(4)' (for instance if C-u is typed
  exactly once right before the command is invoked), then the
  result is %s.

* If the prefix argument is `(16)' (for instance if C-u is typed
  exactly twice right before the command is invoked), then the
  result is %s.

* If any other prefix argument is used (for instance if C-u is
  typed thrice right before the command is invoked), then the
  result is %s." comment (nth 1 norm0) (nth 1 norm1) (nth 1 norm2) (nth 1 norm3))

       ;; All the commands generated by the macro are interactive.
       ;; Those called from a goal, grab the value present there (if any)
       ;; Whereas those called globally always use a prompt
       (interactive ,(pcase spec
                       (`(fromgoal ,_want)
                        "P")
                       (`(global ,prompt)
                        (if prompt
                            (concat "P\nM" prompt ": ")
                          "P"))))
       ;; Depending on the prefix's value we pick one of the three
       ;; normalisation levels
       (let ((,eval (cond ((null ,prefix)
                           ,(car norm0))
                          ((equal ,prefix '(4))
                           ,(car norm1))
                          ((equal ,prefix '(16))
                           ,(car norm2))
                          (t ,(car norm3)))))
       ;; Finally, if the command is called from a goal, we use `agda2-goal-cmd'
       ;; Otherwise we resort to `agda2-go'
         ,(pcase spec
            (`(fromgoal ,want)
             `(agda2-goal-cmd (concat ,cmd " " ,eval) nil ,want))
            (`(global ,prompt)
             `(agda2-go nil t 'busy t
                        (concat ,cmd " "
                                ,eval " "
                                (if ,prompt
                                    (agda2-string-quote (car ,args))
                                    "")))))))))

(defmacro agda2-maybe-normalised (name comment cmd want)
  "Define a command NAME.
COMMENT is a string that will be added to the docstring of NAME.
CMD is the command that will be sent out to Agda.  WANT is an a
query string that may optionally be nil."
  `(agda2-proto-maybe-normalised
    ,name ,comment ,cmd
    ("Simplified"   "simplified")
    ("Instantiated" "neither explicitly normalised nor simplified")
    ("Normalised"   "normalised")
    ("HeadNormal"   "head normalised")
    (fromgoal ,want)))

(defmacro agda2-maybe-normalised-asis (name comment cmd want)
  "Define a command NAME.
COMMENT is a string that will be added to the docstring of NAME.
CMD is the command that will be sent out to Agda.  WANT is an a
query string that may optionally be nil."
  `(agda2-proto-maybe-normalised
    ,name ,comment ,cmd
    ("AsIs"       "returned as is")
    ("Simplified" "simplified")
    ("Normalised" "normalised")
    ("HeadNormal" "head normalised")
    (fromgoal ,want)))

(defmacro agda2-maybe-normalised-toplevel (name comment cmd prompt)
  "Define a command NAME.
COMMENT is a string that will be added to the docstring of NAME.
CMD is the command that will be sent out to Agda.  PROMPT is an a
query string that may optionally be nil."
  `(agda2-proto-maybe-normalised
    ,name ,comment ,cmd
    ("Simplified"   "simplified")
    ("Instantiated" "neither explicitly normalised nor simplified")
    ("Normalised"   "normalised")
    ("HeadNormal"   "head normalised")
    (global ,prompt)))

(defmacro agda2-maybe-normalised-toplevel-asis-noprompt (name comment cmd)
  "Define a command NAME.
COMMENT is a string that will be added to the docstring of NAME.
CMD is the command that will be sent out to Agda."
  `(agda2-proto-maybe-normalised
    ,name ,comment ,cmd
    ("AsIs"       "returned as is")
    ("Simplified" "simplified")
    ("Normalised" "normalised")
    ("HeadNormal" "head normalised")
    (global nil)))

(agda2-maybe-normalised
 agda2-goal-type
 "Show the type of the goal at point"
 "Cmd_goal_type"
 nil)

(agda2-maybe-normalised
 agda2-infer-type
 "Infer the type of the goal at point"
 "Cmd_infer"
 "expression to type")

(agda2-maybe-normalised-toplevel
   agda2-infer-type-toplevel
   "Infers the type of the given expression. The scope used for
the expression is that of the last point inside the current
top-level module"
   "Cmd_infer_toplevel"
   "Expression")

(defun agda2-infer-type-maybe-toplevel ()
  "Infers the type of the given expression.
Either uses the scope of the current goal or, if point is not in a goal, the
top-level scope."
  (interactive)
  (call-interactively (if (agda2-goal-at (point))
                          #'agda2-infer-type
                        #'agda2-infer-type-toplevel)))

(defun agda2-why-in-scope ()
  "Explain why something is in scope in a goal."
  (interactive)
  (agda2-goal-cmd "Cmd_why_in_scope" nil "Name"))

(defun agda2-why-in-scope-toplevel (name)
  "Explain why NAME is in scope at the top level."
  (interactive "MName: ")
  (agda2-go nil t 'busy t
            "Cmd_why_in_scope_toplevel"
            (agda2-string-quote name)))

(defun agda2-why-in-scope-maybe-toplevel ()
  "Explains why a given name is in scope."
  (interactive)
  (call-interactively (if (agda2-goal-at (point))
                          #'agda2-why-in-scope
                          #'agda2-why-in-scope-toplevel)))

(agda2-maybe-normalised
 agda2-elaborate-give
 "Elaborate check the given expression against the hole's type and fill in the
 hole with the elaborated term"
 "Cmd_elaborate_give"
 "expression to elaborate and give")

(agda2-maybe-normalised
 agda2-goal-and-context
 "Shows the type of the goal at point and the currect context"
 "Cmd_goal_type_context"
 nil)

(agda2-maybe-normalised
 agda2-goal-and-context-and-inferred
 "Shows the context, the goal and the given expression's inferred type"
 "Cmd_goal_type_context_infer"
 "expression to type")

(agda2-maybe-normalised
 agda2-goal-and-context-and-checked
 "Shows the context, the goal and check the given expression's against
 the hole's type"
 "Cmd_goal_type_context_check"
 "expression to type")

(agda2-maybe-normalised
 agda2-show-context
 "Show the context of the goal at point"
 "Cmd_context"
 nil)

(agda2-maybe-normalised-asis
 agda2-helper-function-type
  "Compute the type of a hypothetical helper function."
  "Cmd_helper_function"
  "Expression")

(agda2-maybe-normalised
  agda2-module-contents
  "Shows all the top-level names in the given module.
Along with their types."
  "Cmd_show_module_contents"
  "Module name (empty for current module)")

(agda2-maybe-normalised-toplevel
  agda2-module-contents-toplevel
  "Shows all the top-level names in the given module.
Along with their types."
  "Cmd_show_module_contents_toplevel"
  "Module name (empty for top-level module)")

(agda2-maybe-normalised-toplevel
  agda2-search-about-toplevel
  "Search About an identifier"
  "Cmd_search_about_toplevel"
  "Name")

(defun agda2-module-contents-maybe-toplevel ()
  "Show all the top-level names in the given module.
Along with their types.

Uses either the scope of the current goal or, if point is not in
a goal, the top-level scope."
  (interactive)
  (call-interactively (if (agda2-goal-at (point))
                          'agda2-module-contents
                        'agda2-module-contents-toplevel)))

(defun agda2-solve-maybe-all ()
  "Solves goals that are already instantiated internally.
Either only one if point is a goal, or all of them."
  (interactive)
  (call-interactively (if (agda2-goal-at (point))
                          'agda2-solveOne
                          'agda2-solveAll)))

(defun agda2-auto-maybe-all ()
  "Run auto.
Either only one if point is a goal, or all of them."
  (interactive)
  (call-interactively (if (agda2-goal-at (point))
                          'agda2-autoOne
                          'agda2-autoAll)))

(agda2-maybe-normalised-toplevel-asis-noprompt
 agda2-show-goals
 "Show all goals."
 "Cmd_metas")

(agda2-maybe-normalised-toplevel-asis-noprompt
 agda2-solveAll
 "Solves all goals that are already instantiated internally."
 "Cmd_solveAll")

(agda2-maybe-normalised
  agda2-solveOne
  "Solves the goal at point if it is already instantiated internally"
  "Cmd_solveOne"
  nil)

(defun agda2-solveAll-action (iss)
  "Call `agda2-solve-action' on every pair of the the plist ISS.
The key of the plist is a goal, and the value is a string that
ought to be inserted."
  (declare (agda2-command list))
  (while iss
    (let* ((g (pop iss)) (txt (pop iss))
           (cmd (cons #'agda2-solve-action (cons g (cons txt nil)))))
      (if (null agda2-last-responses)
          (push (cons 1 cmd) agda2-last-responses)
        (nconc agda2-last-responses (cons (cons 3 cmd) nil))))))

(defun agda2-solve-action (goal text)
  "Try to satisfy GOAL by inserting TEXT."
  (save-excursion
    (agda2-replace-goal goal text)
    (agda2-goto-goal goal)
    (agda2-give)))

(defun agda2-compute-normalised (&optional arg)
  "Compute the normal form of the expression in the goal at point.

With the prefix argument ARG `(4)' \"abstract\" is ignored during the
computation.

With a prefix argument ARG `(16)' the normal form of
\"show <expression>\" is computed, and then the resulting string
is printed.

With any other prefix the head normal form is computed."
  (interactive "P")
  (let ((cmd (concat "Cmd_compute"
                      (cond ((null arg) " DefaultCompute")
                            ((equal arg '(4)) " IgnoreAbstract")
                            ((equal arg '(16)) " UseShowInstance")
                            (" HeadCompute")))))
    (agda2-goal-cmd cmd nil "expression to normalise")))

(defun agda2-compute-normalised-toplevel (expr &optional arg)
  "Compute the normal form of the given expression EXPR.
The scope used for the expression is that of the last point
inside the current top-level module.

With a prefix argument ARG distinct from `(4)' the normal form of
\"show <expression>\" is computed, and then the resulting string
is printed.

With the prefix argument ARG `(4)' \"abstract\" is ignored during the
computation."
  (interactive "MExpression: \nP")
  (let ((cmd (concat "Cmd_compute_toplevel"
                     (cond ((null arg) " DefaultCompute")
                            ((equal arg '(4)) " IgnoreAbstract")
                            ((equal arg '(16)) " UseShowInstance")
                            (" HeadCompute")) " ")))
    (agda2-go nil t 'busy t
              (concat cmd (agda2-string-quote expr)))))

(defun agda2-compute-normalised-maybe-toplevel ()
  "Compute the normal form of the given expression.
The scope used for the expression is that of the last point
inside the current top-level module.

With a prefix argument distinct from `(4)' the normal form of
\"show <expression>\" is computed, and then the resulting string
is printed.

With the prefix argument `(4)' \"abstract\" is ignored during the
computation."
  (interactive)
  (if (agda2-goal-at (point))
      (call-interactively #'agda2-compute-normalised)
    (call-interactively #'agda2-compute-normalised-toplevel)))

(defun agda2-display-program-version ()
  "Display version of Agda."
  (interactive)
  (agda2-go nil nil 'busy t "Cmd_show_version"))

(defun agda2-highlight-reload ()
  "Load precomputed syntax highlighting info for the current buffer.
Only if the buffer is unmodified, and only if there is anything to load."
 (unless (buffer-modified-p)
   (agda2-go nil t 'not-so-busy t
             "Cmd_load_highlighting_info"
             (agda2-string-quote (buffer-file-name)))))

(defun agda2-literate-p ()
  "Is the current buffer a literate Agda buffer?"
  (not (equal (file-name-extension (buffer-file-name)) "agda")))

(defun agda2-goals-action (goals)
  "Annotates the goals in the current buffer with text properties.
GOALS is a list of the buffer's goal numbers, in the order in
which they appear in the buffer.  Note that this function should
be run /after/ syntax highlighting information has been loaded,
because the two highlighting mechanisms interact in unfortunate
ways."
  (declare (agda2-command list))
  (agda2-forget-all-goals)
  (let ((literate (agda2-literate-p))
        ;; Don't run modification hooks: we don't want this function to
        ;; trigger agda2-abort-highlighting.
        (inhibit-modification-hooks t)
        stk top)
    (cl-labels ((delims ()
                  (re-search-forward
                   "[?]\\|[{][-!]\\|[-!][}]\\|--\\|^%.*\\\\begin{code}\\|\\\\begin{code}\\|\\\\end{code}\\|```\\|\\#\\+begin_src agda2\\|\\#\\+end_src agda2"
                   nil t))
                ;; is-proper checks whether string s (e.g. "?" or "--") is proper
                ;; i.e., is not part of an identifier.
                ;; comment-starter is true if s starts a comment (e.g. "--")
                (is-proper (s comment-starter)
                  (save-excursion
                    (save-match-data
                      (backward-char (length s))
                      (unless (bolp) (backward-char 1))  ;; bolp = pointer at beginning of line
                      ;; Andreas, 2014-05-17 Issue 1132
                      ;; A questionmark can also follow immediately after a .
                      ;; for instance to be a place holder for a dot pattern.
                      (looking-at (concat "\\([.{}();]\\|^\\|\\s \\)"  ;; \\s = whitespace
                                          (regexp-quote s)
                                          (unless comment-starter
                                            "\\([{}();]\\|$\\|\\s \\)"))))))
                (make (p)          (agda2-make-goal p (point) (pop goals)))
                (inside-comment () (and stk (null     (car stk))))
                (inside-goal ()    (and stk (integerp (car stk))))
                (outside-code ()   (and stk (eq (car stk) 'outside)))
                (inside-code ()    (not (outside-code)))
                ;; inside a multi-line comment ignore everything but the multi-line comment markers
                (safe-delims ()
                  (if (inside-comment)
                      (re-search-forward "{-\\|-}" nil t)
                    (delims))))
      (save-excursion
        ;; In literate mode we should start out in the "outside of code"
        ;; state.
        (if literate (push 'outside stk))
        (goto-char (point-min))
        (while (and goals (safe-delims))
          (pcase (match-string 0)
            ("\\begin{code}"     (when (outside-code)               (pop stk)))
            ("\\end{code}"       (when (not stk)                    (push 'outside stk)))
            ("#+begin_src agda2" (when (outside-code)               (pop stk)))
            ("#+end_src agda2"   (when (not stk)                    (push 'outside stk)))
            ("```"               (if   (outside-code)               (pop stk)
                                   (when (not stk)                    (push 'outside stk))))
            ("--"                (when (and (not stk)
                                            (is-proper "--" t))     (end-of-line)))
            ("{-"                (when (and (inside-code)
                                            (not (inside-goal)))    (push nil           stk)))
            ("-}"                (when (inside-comment)             (pop stk)))
            ("{!"                (when (and (inside-code)
                                            (not (inside-comment))) (push (- (point) 2) stk)))
            ("!}"                (when (inside-goal)
                                   (setq top (pop stk))
                                   (unless stk (make top))))
            ("?"                 (progn
                                   (when (and (not stk) (is-proper "?" nil))
                                     (delete-char -1)
                                     (insert "{!!}")
                                     (make (- (point) 4)))))))))))

(defun agda2-make-goal (p q n)
  "Make a goal with number N at <P>{!...!}<Q>.  Assume the region is clean."
  (with-silent-modifications
    (let ((atp (lambda (x ps) (add-text-properties x (1+ x) ps))))
      (funcall atp p       '(category agda2-delim1))
      (funcall atp (1+ p)  '(category agda2-delim2))
      (funcall atp (- q 2) '(category agda2-delim3))
      (funcall atp (1- q)  '(category agda2-delim4)))
    (let ((o (make-overlay p q nil t nil)))
      (overlay-put o 'modification-hooks '(agda2-protect-goal-markers))
      (overlay-put o 'agda2-gn           n)
      (overlay-put o 'face               'highlight)
      (overlay-put o 'after-string       (propertize (format "%s" n) 'face 'highlight)))))

(defun agda2-protect-goal-markers (ol action beg end &optional _length)
  "Ensure that the goal overlay OL cannot be tampered with.
Except if `inhibit-read-only' is non-nil or /all/ of the goal is
modified.  This function implemented a modification hook.  See
the Info mode `(elisp) Overlay Properties' for more details on
the arguments ACTION, BEG and END."
  (if action
      ;; This is the after-change hook.
      nil
    ;; This is the before-change hook.
    (cond
     ((and (<= beg (overlay-start ol)) (>= end (overlay-end ol)))
      ;; The user is trying to remove the whole goal:
      ;; manually evaporate the overlay and add an undo-log entry so
      ;; it gets re-added if needed.
      (when (listp buffer-undo-list)
        (push (list 'apply 0 (overlay-start ol) (overlay-end ol)
                    'move-overlay ol (overlay-start ol) (overlay-end ol))
              buffer-undo-list))
      (delete-overlay ol))
     ((or (< beg (+ (overlay-start ol) 2))
          (> end (- (overlay-end ol) 2)))
      (barf-if-buffer-read-only)))))

(defun agda2-update (old-g new-txt)
  "Update the goal OLD-G.
If NEW-TXT is a string, then the goal is replaced by the string,
and otherwise the text inside the goal is retained (parenthesised
if NEW-TXT is `'paren').

Removes the goal braces, but does not remove the goal overlay or
text properties."
  (cl-multiple-value-bind (p q) (agda2-range-of-goal old-g)
    (save-excursion
      (cond ((stringp new-txt)
             (agda2-replace-goal old-g new-txt))
            ((eq new-txt 'paren)
             (goto-char (- q 2)) (insert ")")
             (goto-char (+ p 2)) (insert "(")))
      (cl-multiple-value-bind (p q) (agda2-range-of-goal old-g)
        (delete-region (- q 2) q)
        (delete-region p (+ p 2)))
        ;; Update highlighting
        (if (and (not (eq new-txt 'paren)) (not (eq new-txt 'no-paren)))
            (apply 'agda2-go 'save t 'busy nil "Cmd_highlight"
              (format "%d" old-g)
              (agda2-mkRange `(,p ,(- q 2)))
              (agda2-string-quote new-txt) nil)))))

;;;; Miscellaneous

(defun agda2-process-status ()
  "Status of `agda2-process-buffer', or \"no process\"."
  (condition-case nil
      (process-status agda2-process)
    (error "No process")))

(defun agda2-intersperse (sep xs)
  "Insert SEP between every element of XS."
  (let (ys)
    (while xs
      (push (pop xs) ys)
      (push sep ys))
    (pop ys)
    (nreverse ys)))

(defun agda2-goal-Range (o)
  "The Haskell Range of goal overlay O."
  (agda2-mkRange `(,(+ (overlay-start o) 2)
                   ,(- (overlay-end   o) 2))))

(defun agda2-mkRange (points)
  "A string representing a range corresponding to POINTS.
POINTS must be a list of integers, and its length must be 0 or 2."
  (if points
      (format "(intervalsToRange (Just (mkAbsolute %s)) %s)"
              (agda2-string-quote (file-truename (buffer-file-name)))
              (format "[Interval %s %s]"
                      (agda2-mkPos (car points))
                      (agda2-mkPos (cadr points))))
    "noRange"))

(defun agda2-mkPos (&optional p)
  "The Haskell PositionWithoutFile corresponding to P or `point'."
  (save-excursion
    (save-restriction
      (widen)
      (if p (goto-char p))
      (format "(Pn () %d %d %d)"
              (point)
              (count-lines (point-min) (point))
              (1+ (current-column))))))

(defun agda2-char-quote (c)
  "Convert character C to the notation used in Haskell strings.
The non-ASCII characters are actually rendered as
\"\\xNNNN\\&\", i.e. followed by a \"null character\", to avoid
problems if they are followed by digits.  ASCII characters (code
points < 128) are converted to singleton strings."
  (if (< c 128)
      (string c)
    (format "\\x%x\\&" (encode-char c 'ucs))))

(defun agda2-string-quote (s)
  "Format S as a Haskell string literal.
Removes any text properties, escapes newlines, double quotes,
etc., adds surrounding double quotes, and converts non-ASCII
characters to the \\xNNNN notation used in Haskell strings."
  (let ((pp-escape-newlines t)
        (s2 (copy-sequence s)))
    (set-text-properties 0 (length s2) nil s2)
    (mapconcat 'agda2-char-quote (pp-to-string s2) "")))

(defun agda2-list-quote (strings)
  "Convert a list of STRINGS into a string representing it in Haskell syntax."
  (concat "[" (mapconcat 'agda2-string-quote strings ", ") "]"))

(defun agda2-goal-at (pos)
  "Return (goal overlay, goal number) at POS, or nil."
  (let ((os (and pos (overlays-at pos))) o g)
    (while (and os (not (setq g (overlay-get (setq o (pop os)) 'agda2-gn)))))
    (if g (list o g))))

(defun agda2-goal-overlay (goal)
  "Return the overlay of goal number GOAL, if any."
  (catch 'found
    (dolist (ov (overlays-in (point-min) (point-max)))
      (when (equal (overlay-get ov 'agda2-gn) goal)
        (throw 'found ov)))))

(defun agda2-range-of-goal (g)
  "The range of goal G."
  (let ((o (agda2-goal-overlay g)))
    (if o (list (overlay-start o) (overlay-end o)))))

(defun agda2-goto-goal (g)
  "Jump to the goal G."
  (let ((p (+ 2 (car (agda2-range-of-goal g)))))
    (if p (goto-char p))))

(defun agda2-replace-goal (g newtxt)
  "Replace the content of goal G with NEWTXT."
  (interactive)
  (save-excursion
    (cl-multiple-value-bind (p q) (agda2-range-of-goal g)
      (setq p (+ p 2) q (- q 2))
      (let ((indent (and (goto-char p) (current-column))))
        (delete-region p q) (insert newtxt)
        (while (re-search-backward "^" p t)
          (insert-char ?  indent) (backward-char (1+ indent)))))))

(defun agda2-forget-all-goals ()
  "Remove all goal annotations.
\(Including some text properties which might be used by other
\(minor) modes.)"
  (with-silent-modifications
    (remove-text-properties (point-min) (point-max)
                            '(category nil agda2-delim2 nil agda2-delim3 nil
                                       display nil rear-nonsticky nil)))
  (let ((p (point-min)))
    (while (< (setq p (next-single-char-property-change p 'agda2-gn))
              (point-max))
      (delete-overlay (car (agda2-goal-at p))))))

(defun agda2-decl-beginning ()
  "Find the beginning point of the declaration containing the point.
To do: dealing with semicolon separated decls."
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
  "TODO."
  (interactive)
  (goto-char (agda2-decl-beginning)))

(defvar agda2-debug-buffer-name "*Agda debug*"
  "The name of the buffer used for Agda debug messages.")

(defun agda2-verbose (msg)
  "Append the string MSG to the `agda2-debug-buffer-name' buffer.
Note that this buffer's contents is not erased automatically when
a file is loaded."
  (declare (agda2-command string))
  (with-current-buffer (get-buffer-create agda2-debug-buffer-name)
    (save-excursion
      (goto-char (point-max))
      (insert msg))))

;;;; Comments and paragraphs

(defun agda2-comments-and-paragraphs-setup nil
  "Set up comment and paragraph handling for the Agda mode."

  ;; Empty lines (all white space according to Emacs) delimit
  ;; paragraphs.
  (setq-local paragraph-start "\\s-*$")
  (setq-local paragraph-separate paragraph-start)

  ;; Support for adding/removing comments.
  (setq-local comment-start "-- ")

  ;; Use the syntax table to locate comments (and possibly other
  ;; things). Syntax table setup for comments is done elsewhere.
  (setq-local comment-use-syntax t)

  ;; Update token-based highlighting after the buffer has been saved.
  (add-hook 'after-save-hook 'agda2-highlight-tokens nil 'local)

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

(defun agda2-comment-dwim-rest-of-buffer ()
  "Comment or uncomment the rest of the buffer.
From the beginning of the current line to the end of the buffer."
  (interactive)
  (save-excursion
    (forward-line 0)
    (push-mark (point) 'no-message 'activate-mark)
    (unwind-protect
        (progn
          (goto-char (point-max))
          (comment-dwim nil))
      (pop-mark))))

(defun agda2-highlight-tokens nil
  "Compute token-based highlighting information.

Unless the user option `agda2-highlight-level' is `none' or the
Agda process is busy (or `not-so-busy') with something.  This
command might save the buffer."
  (unless (or agda2-in-progress
              (eq agda2-highlight-level 'none))
    (agda2-go 'save t 'not-so-busy t
              "Cmd_tokenHighlighting"
              (agda2-string-quote (buffer-file-name))
              "Keep")))

;;;; Xref inregration

(defun agda2-xref-backend ()
  "Return an Xref backend."
  'agda2)

;; The default implementation of `xref-backend-identifier-at-point' is
;; fine and doesn't have to be changed.

(cl-defmethod xref-backend-identifier-at-point ((_ (eql 'agda2)))
  "Return the symbol at point with text properties."
  (thing-at-point 'symbol))

;; (cl-defmethod xref-backend-identifier-completion-table ((_ (eql 'agda2)))
;;   "Generate a list of possible candidates."
;;   (lambda (string pred action)
;;     ))

(cl-defmethod xref-backend-definitions ((_ (eql 'agda2)) ident)
  "Generate a list of definitions for identifier IDENT."
  (let ((xref-info (get-text-property 0 'agda2-xref-info ident)))
    (and xref-info
         (let ((loc (xref-make-buffer-location
                     (find-file-noselect (car xref-info))
                     (cdr xref-info))))
           (list (xref-make ident loc))))))

;; (cl-defmethod xref-backend-references ((_ (eql 'agda2)) identifier)
;;   "Generate a list of references for IDENTIFIER.")

;; (cl-defmethod xref-backend-apropos ((_ (eql 'agda2)) pattern)
;;   "Generate a list of definitions matching PATTERN.")

(defun agda2-maybe-goto (filepos)
  "Might move point to the given error.
FILEPOS should have the form (FILE . POSITION).

If `agda2-highlight-in-progress' is nil, then nothing happens.
Otherwise, if the current buffer is the one that is connected to
the Agda process, then point is moved to POSITION in
FILE (assuming that the FILE is readable).  Otherwise point is
moved to the given position in the buffer visiting the file, if
any, and in every window displaying the buffer, but the window
configuration and the selected window are not changed."
  (declare (agda2-command cons))
  (when (and agda2-highlight-in-progress
             (consp filepos)
             (stringp (car filepos))
             (integerp (cdr filepos)))
    (xref-push-marker-stack)
    (set-buffer (find-file-noselect (car filepos)))
    (goto-char (cdr filepos))))

;;;; Implicit arguments

(defun agda2-display-implicit-arguments (&optional arg)
  "Toggle display of implicit arguments.
With prefix argument or a non-nil value for ARG, turn on display
of implicit arguments if the argument is a positive number,
otherwise turn it off."
  (interactive "P")
  (cond
   ((null arg)
    (agda2-go nil t 'not-so-busy t "ToggleImplicitArgs"))
   ((and (numberp arg) (> arg 0))
      (agda2-go nil t 'not-so-busy t "ShowImplicitArgs" "True"))
   (t (agda2-go nil t 'not-so-busy t "ShowImplicitArgs" "False"))))

;;;; Irrelevant arguments

(defun agda2-display-irrelevant-arguments (&optional arg)
  "Toggle display of irrelevant arguments.
With prefix argument or a non-nil argument for ARG, turn on
display of irrelevant arguments if the argument is a positive
number, otherwise turn it off."
  (interactive "P")
  (cond
   ((null arg)
    (agda2-go nil t 'not-so-busy t "ToggleIrrelevantArgs"))
   ((and (numberp arg) (> arg 0))
      (agda2-go nil t 'not-so-busy t "ShowIrrelevantArgs" "True"))
   (t (agda2-go nil t 'not-so-busy t "ShowIrrelevantArgs" "False"))))

;;;; The pop-up menu

(defun agda2-popup-menu-3 (ev)
  "If in a goal, popup the goal menu and call chosen command.
EV is the event object associated with a click."
  (interactive "e")
  (let (choice)
    (save-excursion
      (and (agda2-goal-at (goto-char (posn-point (event-end ev))))
           (setq choice (x-popup-menu ev agda2-goal-menu))
           (call-interactively
            (lookup-key agda2-goal-menu (apply 'vector choice)))))))

;;;; Switching to a different version of Agda

(defun agda2-get-agda-program-versions ()
  "Attempt to detect available Agda versions."
  (let (versions)
    (dolist (dir (if (fboundp 'exec-path) (exec-path) exec-path))
      (when (file-accessible-directory-p dir)
        (dolist (file (directory-files dir t))
          (let ((base (file-name-nondirectory file)))
            (when (and (file-regular-p file) (file-executable-p file)
                       (string-match "\\`agda-mode-\\(.+\\)" base))
              (push (match-string 1 base) versions))))))
    (delete-dups versions)))

;; Note that other versions of Agda may use different protocols, so
;; this function unloads the Emacs mode.

(defun agda2-set-program-version (version)
  "Try to switch to Agda version VERSION.

This command assumes that the agda and agda-mode executables for
Agda version VERSION are called agda-VERSION and
agda-mode-VERSION, and that they are located on the PATH.  (If
VERSION is empty, then agda and agda-mode are used instead.)

An attempt is made to preserve the default value of
`agda2-mode-hook'."
  (interactive
   (list (completing-read "Version: " (agda2-get-agda-program-versions))))

  (let*
      ((agda-buffers
        (cl-remove-if-not
         (lambda (buf)
           (eq (buffer-local-value 'major-mode buf) 'agda2-mode))
         (buffer-list)))

       (default-hook (default-value 'agda2-mode-hook))

       (version-suffix (if (member version '("" nil))
                           ""
                         (concat "-" version)))

       ;; Run agda-mode<version-suffix> and make sure that it returns
       ;; successfully.
       (coding-system-for-read 'utf-8)
       (agda-mode-prog (concat "agda-mode" version-suffix))
       (agda-mode-path
        (condition-case nil
            (with-temp-buffer
              (unless
                  (zerop (call-process agda-mode-prog
                                       nil (current-buffer) nil
                                       "locate"))
                (error "%s" (concat "Error when running "
                                    agda-mode-prog)))
              (buffer-string))
          (file-error
           (error "%s" (concat "Could not find " agda-mode-prog))))))

    ;; Make sure that agda-mode<version-suffix> returns a valid file.
    (unless (file-readable-p agda-mode-path)
      (error "%s" (concat "Could not read " agda-mode-path)))

    ;; Turn off the Agda mode.
    (agda2-quit)

    ;; Kill some buffers related to Agda.
    (when (buffer-live-p agda2-info-buffer)
      (kill-buffer agda2-info-buffer))
    (when (and agda2-debug-buffer-name
               (get-buffer agda2-debug-buffer-name))
      (kill-buffer agda2-debug-buffer-name))

    ;; Remove the Agda mode directory from the load path.
    (setq load-path (delete agda2-directory load-path))

    ;; Unload the Agda mode and its dependencies.
    (unload-feature 'agda2-mode      'force)
    (unload-feature 'agda2           'force)
    (unload-feature 'eri             'force)
    (unload-feature 'agda-input      'force)
    (unload-feature 'agda2-highlight 'force)
    (unload-feature 'agda2-abbrevs   'force)

    ;; Load the new version of Agda.
    (load-file agda-mode-path)
    (require 'agda2-mode)
    (setq agda2-program-name (concat "agda" version-suffix))

    ;; Restore the Agda mode's default hook (if any).
    (when default-hook
      (set-default 'agda2-mode-hook default-hook))

    ;; Restart the Agda mode in all former Agda mode buffers.
    (mapc (lambda (buf)
            (with-current-buffer buf
              (agda2-mode)))
          agda-buffers)))

(provide 'agda2-mode)
;;; agda2-mode.el ends here

; LocalWords:  Agda
