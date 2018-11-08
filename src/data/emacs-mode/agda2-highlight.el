;;; agda2-highlight.el --- Syntax highlighting for Agda (version ≥ 2)

;;; Commentary:

;; Code to apply syntactic highlighting to Agda source code. This uses
;; Agda's own annotations to figure out what is what, so the parsing
;; is always done correctly, but highlighting is not done on the fly.

;;; Code:

(require 'annotation)
(require 'font-lock)

(defgroup agda2-highlight nil
  "Syntax highlighting for Agda."
  :group 'agda2)

(defcustom agda2-highlight-level 'non-interactive
  "How much syntax highlighting should be produced?
Interactive highlighting includes highlighting of the expression
that is currently being type-checked."
  :type '(choice
          (const :tag "None"            none)
          (const :tag "Non-interactive" non-interactive)
          (const :tag "Interactive"     interactive))
  :group 'agda2-highlight)

(defun agda2-highlight-level nil
  "Formats the highlighting level in a Haskelly way."
  (cond ((equal agda2-highlight-level 'none)            "None")
        ((equal agda2-highlight-level 'non-interactive) "NonInteractive")
        ((equal agda2-highlight-level 'interactive)     "Interactive")
        (t                                              "None")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for setting faces

(defun agda2-highlight-set-face-attribute (face attrs)
  "Reset (globally) all attributes of the face FACE according to ATTRS.
If the face does not exist, then it is created first."
  (make-face face)
  (set-face-attribute face nil
                      :family         'unspecified
                      :width          'unspecified
                      :height         'unspecified
                      :weight         'unspecified
                      :slant          'unspecified
                      :foreground     'unspecified
                      :background     'unspecified
                      :inverse-video  'unspecified
                      :stipple        'unspecified
                      :underline      'unspecified
                      :overline       'unspecified
                      :strike-through 'unspecified
                      :inherit        'unspecified
                      :box            'unspecified
                      :font           'unspecified)
  (eval `(set-face-attribute face nil ,@attrs)))

(defvar agda2-highlight-face-attributes-list
  '(:family :width :height :weight :slant :foreground :background
            :inverse-video :stipple :underline :overline :strike-through
            :inherit :box :font)
  "The attributes considered by `agda2-highlight-face-attributes'.")

(defun agda2-highlight-face-attributes (face)
  "The names and values of all attributes in FACE.
Only the attributes in `agda2-highlight-face-attributes-list' are
considered. The attributes are returned in a flat list of the
form (name1 value1 name2 value2...)."
  (apply 'append
         (mapcar (lambda (attr)
                   (let ((val (face-attribute face attr)))
                     (if (member val '(unspecified nil)) '()
                       (list attr (if (symbolp val) `',val val)))))
                 agda2-highlight-face-attributes-list)))

(defun agda2-highlight-set-faces (variable group)
  "Set all Agda faces according to the value of GROUP.
Also sets the default value of VARIABLE to GROUP."
  (set-default variable group)
  (mapc (lambda (face-and-attrs)
          (agda2-highlight-set-face-attribute
           (car face-and-attrs) (cdr face-and-attrs)))
        (cond
         ((equal group 'conor)
          '((agda2-highlight-keyword-face
             :bold t)
            (agda2-highlight-string-face
             :foreground "firebrick3")
            (agda2-highlight-number-face
             :foreground "firebrick3")
            (agda2-highlight-symbol-face
             :foreground "grey25")
            (agda2-highlight-primitive-type-face
             :foreground "medium blue")
            (agda2-highlight-bound-variable-face
             :foreground "purple")
            (agda2-highlight-inductive-constructor-face
             :foreground "firebrick3")
            (agda2-highlight-coinductive-constructor-face
             :foreground "firebrick3")
            (agda2-highlight-datatype-face
             :foreground "medium blue")
            (agda2-highlight-field-face
             :foreground "deeppink")
            (agda2-highlight-function-face
             :foreground "darkgreen")
            (agda2-highlight-module-face
             :foreground "medium blue")
            (agda2-highlight-postulate-face
             :foreground "darkgreen")
            (agda2-highlight-primitive-face
             :foreground "darkgreen")
            (agda2-highlight-macro-face
             :foreground "aquamarine4")
            (agda2-highlight-record-face
             :foreground "medium blue")
            (agda2-highlight-dotted-face)
            (agda2-highlight-error-face
             :foreground "red"
             :underline t)
            (agda2-highlight-unsolved-meta-face
             :foreground "black"
             :background "yellow")
            (agda2-highlight-unsolved-constraint-face
             :foreground "black"
             :background "yellow")
            (agda2-highlight-termination-problem-face
             :foreground "black"
             :background "light salmon")
            (agda2-highlight-positivity-problem-face
             :foreground "black"
             :background "peru")
            (agda2-highlight-incomplete-pattern-face
             :foreground "black"
             :background "purple")
            (agda2-highlight-typechecks-face
             :foreground "black"
             :background "light blue")))
         ((equal group 'default-faces)
          (list (cons 'agda2-highlight-keyword-face
                      (agda2-highlight-face-attributes
                       font-lock-keyword-face))
                (cons 'agda2-highlight-string-face
                      (agda2-highlight-face-attributes
                       font-lock-string-face))
                (cons 'agda2-highlight-number-face
                      (agda2-highlight-face-attributes
                       font-lock-constant-face))
                (cons 'agda2-highlight-symbol-face
                      (agda2-highlight-face-attributes
                       font-lock-keyword-face))
                (cons 'agda2-highlight-primitive-type-face
                      (agda2-highlight-face-attributes
                       font-lock-keyword-face))
                (cons 'agda2-highlight-bound-variable-face
                      (agda2-highlight-face-attributes
                       font-lock-variable-name-face))
                (cons 'agda2-highlight-inductive-constructor-face
                      (agda2-highlight-face-attributes
                       font-lock-type-face))
                (cons 'agda2-highlight-coinductive-constructor-face
                      (agda2-highlight-face-attributes
                       font-lock-type-face))
                (cons 'agda2-highlight-datatype-face
                      (agda2-highlight-face-attributes
                       font-lock-type-face))
                (cons 'agda2-highlight-field-face
                      (agda2-highlight-face-attributes
                       font-lock-variable-name-face))
                (cons 'agda2-highlight-function-face
                      (agda2-highlight-face-attributes
                       font-lock-function-name-face))
                (cons 'agda2-highlight-module-face
                      (agda2-highlight-face-attributes
                       font-lock-type-face))
                (cons 'agda2-highlight-postulate-face
                      (agda2-highlight-face-attributes
                       font-lock-type-face))
                (cons 'agda2-highlight-primitive-face
                      (agda2-highlight-face-attributes
                       font-lock-constant-face))
                (cons 'agda2-highlight-macro-face
                      (agda2-highlight-face-attributes
                       font-lock-function-name-face))
                (cons 'agda2-highlight-record-face
                      (agda2-highlight-face-attributes
                       font-lock-variable-name-face))
                (cons 'agda2-highlight-dotted-face
                      (agda2-highlight-face-attributes
                       font-lock-variable-name-face))
                (cons 'agda2-highlight-operator-face
                      (agda2-highlight-face-attributes
                       font-lock-function-name-face))
                (cons 'agda2-highlight-error-face
                      (agda2-highlight-face-attributes
                       font-lock-warning-face))
                (cons 'agda2-highlight-typechecks-face
                      (agda2-highlight-face-attributes
                       font-lock-type-face))
                (cons 'agda2-highlight-typechecking-face
                      (agda2-highlight-face-attributes
                       font-lock-preprocessor-face)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Faces

(defcustom agda2-highlight-face-groups nil
  "Colour scheme used in Agda buffers.
Changes to this variable may not take full effect until you have
restarted Emacs. Note also that if you are using the
default-faces option and change your colour theme, then the
changes may not take effect in Agda buffers until you have
restarted Emacs."
  :type '(choice
          (const :tag "Use the settings in the \"Agda2 Highlight Faces\" subgroup." nil)
          (const :tag "Use an approximation of Conor McBride's colour scheme."
                 conor)
          (const :tag "Use simplified highlighting and default font-lock faces."
                 default-faces))
  :group 'agda2-highlight
  :set 'agda2-highlight-set-faces)

(defgroup agda2-highlight-faces nil
  "Faces used to highlight Agda code.
If `agda2-highlight-face-groups' is nil."
  :group 'agda2-highlight)

(defface agda2-highlight-keyword-face
  '((t (:foreground "DarkOrange3")))
  "The face used for keywords."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-string-face
  '((t (:foreground "firebrick")))
  "The face used for strings."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-number-face
  '((t (:foreground "purple")))
  "The face used for numbers."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-symbol-face
  '((((background light))
     (:foreground "gray25"))
    (((background dark))
     (:foreground "gray75")))
  "The face used for symbols like forall, =, ->, etc."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-primitive-type-face
  '((t (:foreground "medium blue")))
  "The face used for primitive types (like Set and Prop)."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-bound-variable-face
  '((t nil))
  "The face used for bound variables."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-inductive-constructor-face
  '((t (:foreground "green4")))
  "The face used for inductive constructors."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-coinductive-constructor-face
  '((t (:foreground "gold4")))
  "The face used for coinductive constructors."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-datatype-face
  '((t (:foreground "medium blue")))
  "The face used for datatypes."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-field-face
  '((t (:foreground "DeepPink2")))
  "The face used for record fields."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-function-face
  '((t (:foreground "medium blue")))
  "The face used for functions."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-module-face
  '((t (:foreground "purple")))
  "The face used for module names."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-postulate-face
  '((t (:foreground "medium blue")))
  "The face used for postulates."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-pragma-face
  '((t nil))
  "The face used for (some text in) pragmas."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-primitive-face
  '((t (:foreground "medium blue")))
  "The face used for primitive functions."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-macro-face
  '((t (:foreground "aquamarine4")))
  "The face used for macros."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-record-face
  '((t (:foreground "medium blue")))
  "The face used for record types."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-dotted-face
  '((t nil))
  "The face used for dotted patterns."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-operator-face
  '((t nil))
  "The face used for operators."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-error-face
  '((t (:foreground "red" :underline t)))
  "The face used for errors."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-unsolved-meta-face
  '((t (:background "yellow")))
  "The face used for unsolved meta variables."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-unsolved-constraint-face
  '((t (:background "yellow")))
  "The face used for unsolved constraints which are not connected to metas."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-termination-problem-face
  '((t (:background "light salmon")))
  "The face used for termination problems."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-positivity-problem-face
  '((t (:background "peru")))
  "The face used for positivity problems."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-deadcode-face
  '((t (:background "dark gray")))
  "The face used for dead code (unreachable clauses, etc.)."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-coverage-problem-face
  '((t (:background "wheat")))
  "The face used for coverage problems."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-catchall-clause-face
  '((t (:background "white smoke")))
  "The face used for catchall clauses."
  :group 'agda2-highlight-faces)

(defface agda2-highlight-typechecks-face
  '((t (:background "light blue"
        :foreground "black")))
  "The face used for code which is being type-checked."
  :group 'agda2-highlight-faces)

(defvar agda2-highlight-faces
  '((keyword                . agda2-highlight-keyword-face)
    (comment                . font-lock-comment-face)
    (background             . font-lock-comment-face)
    (markup                 . font-lock-comment-face)
    (string                 . agda2-highlight-string-face)
    (number                 . agda2-highlight-number-face)
    (symbol                 . agda2-highlight-symbol-face)
    (primitivetype          . agda2-highlight-primitive-type-face)
    (bound                  . agda2-highlight-bound-variable-face)
    (inductiveconstructor   . agda2-highlight-inductive-constructor-face)
    (coinductiveconstructor . agda2-highlight-coinductive-constructor-face)
    (datatype               . agda2-highlight-datatype-face)
    (field                  . agda2-highlight-field-face)
    (function               . agda2-highlight-function-face)
    (module                 . agda2-highlight-module-face)
    (postulate              . agda2-highlight-postulate-face)
    (pragma                 . agda2-highlight-pragma-face)
    (primitive              . agda2-highlight-primitive-face)
    (macro                  . agda2-highlight-macro-face)
    (record                 . agda2-highlight-record-face)
    (dotted                 . agda2-highlight-dotted-face)
    (operator               . agda2-highlight-operator-face)
    (error                  . agda2-highlight-error-face)
    (unsolvedmeta           . agda2-highlight-unsolved-meta-face)
    (unsolvedconstraint     . agda2-highlight-unsolved-constraint-face)
    (terminationproblem     . agda2-highlight-termination-problem-face)
    (deadcode               . agda2-highlight-deadcode-face)
    (coverageproblem        . agda2-highlight-coverage-problem-face)
    (positivityproblem      . agda2-highlight-positivity-problem-face)
    (incompletepattern      . agda2-highlight-incomplete-pattern-face)
    (catchallclause         . agda2-highlight-catchall-clause-face)
    (typechecks             . agda2-highlight-typechecks-face))
  "Alist mapping code aspects to the face used when displaying them.

The aspects currently recognised are the following:

`bound'                  Bound variables.
`coinductiveconstructor' Coinductive constructors.
`datatype'               Data types.
`dotted'                 Dotted patterns.
`error'                  Errors.
`field'                  Record fields.
`function'               Functions.
`incompletepattern'      Incomplete patterns.
`inductiveconstructor'   Inductive constructors.
`keyword'                Keywords.
`module'                 Module names.
`number'                 Numbers.
`operator'               Operators.
`postulate'              Postulates.
`pragma'                 Text occurring in pragmas that does not have
                           a more specific (syntactic) aspect.
`primitive'              Primitive functions.
`primitivetype'          Primitive types (like Set and Prop).
`macro'                  Macros.
`record'                 Record types.
`string'                 Strings.
`symbol'                 Symbols like forall, =, ->, etc.
`terminationproblem'     Termination problems.
`positivityproblem'      Positivity problems.
`deadcode'               Deadcode (like unreachable clauses or RHS)
`coverageproblem'        Coverage problems.
`catchallclause'         Clause not holding definitionally.
`typechecks'             Code which is being type-checked.
`unsolvedconstraint'     Unsolved constraints, not connected to meta
                           variables.
`unsolvedmeta'           Unsolved meta variables.
`background'             Non-Agda code contents in literate mode.
`markup'                 Delimiters to separate the Agda code blocks
                           from other contents
`comment'                Comments.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Variables

(defvar agda2-highlight-in-progress nil
  "If nil, then highlighting annotations are not applied.")
(make-variable-buffer-local 'agda2-highlight-in-progress)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions

(defun agda2-highlight-setup nil
  "Set up the `annotation' library for use with `agda2-mode'."
  (agda2-highlight-set-faces 'agda2-highlight-face-groups agda2-highlight-face-groups)
  (setq annotation-bindings agda2-highlight-faces))

(defun agda2-highlight-apply (remove &rest cmds)
  "Adds the syntax highlighting information in the annotation list CMDS.

If REMOVE is nil, then old syntax highlighting information is not
removed. Otherwise all token-based syntax highlighting is removed."
  (let (;; Ignore read-only status, otherwise this function may fail.
        (inhibit-read-only t))
    (apply 'annotation-load
           "Click mouse-2 to jump to definition"
           remove
           cmds)))

(defun agda2-highlight-add-annotations (remove &rest cmds)
  "Like `agda2-highlight-apply'.
But only if `agda2-highlight-in-progress' is non-nil."
  (if agda2-highlight-in-progress
      (apply 'agda2-highlight-apply remove cmds)))

(defun agda2-highlight-load (file)
  "Load syntax highlighting information from FILE.

Old syntax highlighting information is not removed."
  (let* ((coding-system-for-read 'utf-8)
         (cmds (with-temp-buffer
                 (insert-file-contents file)
                 (goto-char (point-min))
                 (read (current-buffer)))))
      (apply 'agda2-highlight-apply cmds)))

(defun agda2-highlight-load-and-delete-action (file)
  "Like `agda2-highlight-load', but deletes FILE when done.
And highlighting is only updated if `agda2-highlight-in-progress'
is non-nil."
  (unwind-protect
      (if agda2-highlight-in-progress
          (agda2-highlight-load file))
    (delete-file file)))

(defun agda2-highlight-clear (&optional token-based)
  "Remove all syntax highlighting.

If TOKEN-BASED is non-nil, then only token-based highlighting is
removed."
  (interactive)
  (let ((inhibit-read-only t))
       ; Ignore read-only status, otherwise this function may fail.
    (annotation-remove-annotations token-based)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda2-highlight)
;;; agda2-highlight.el ends here
