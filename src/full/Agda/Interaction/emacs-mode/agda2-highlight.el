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

(defun agda2-highlight-set-faces (variable group)
  "Set all Agda faces according to the value of GROUP.
Also sets the default value of VARIABLE to GROUP."
  (set-default variable group)
  (mapc (lambda (face-and-attrs)
          (agda2-highlight-set-face-attribute
           (car face-and-attrs) (cdr face-and-attrs)))
        (cond
         ((equal group 'conor)
          '((agda2-highlight-comment-face
             :foreground "gray35")
            (agda2-highlight-keyword-face
             :underline t)
            (agda2-highlight-string-face)
            (agda2-highlight-number-face)
            (agda2-highlight-symbol-face)
            (agda2-highlight-primitive-type-face
             :foreground "blue")
            (agda2-highlight-bound-variable-face
             :foreground "purple")
            (agda2-highlight-inductive-constructor-face
             :foreground "dark red")
            (agda2-highlight-coinductive-constructor-face
             :foreground "dark red")
            (agda2-highlight-datatype-face
             :foreground "blue")
            (agda2-highlight-field-face
             :foreground "dark red")
            (agda2-highlight-function-face
             :foreground "dark green")
            (agda2-highlight-module-face
             :foreground "dark green")
            (agda2-highlight-postulate-face
             :foreground "dark green")
            (agda2-highlight-primitive-face
             :foreground "dark green")
            (agda2-highlight-record-face
             :foreground "blue")
            (agda2-highlight-dotted-face)
            (agda2-highlight-error-face
             :foreground "black"
             :background "sandy brown")
            (agda2-highlight-unsolved-meta-face
             :foreground "black"
             :background "gold")
            (agda2-highlight-termination-problem-face
             :foreground "black"
             :background "red")
            (agda2-highlight-incomplete-pattern-face
             :foreground "black"
             :background "purple"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Faces

(defcustom agda2-highlight-face-groups nil
  "Colour scheme to use for agda2 highlight faces.
Note that changing this option does not remove the customisations
below; you can get them back by resetting this option and
restarting Emacs."
  :type '(choice
            (const :tag "Use the settings below." nil)
            (const :tag "Use an approximation of Conor McBride's colour scheme."
                   conor))
  :group 'agda2-highlight
  :set 'agda2-highlight-set-faces)

(defface agda2-highlight-comment-face
  '((t (:foreground "firebrick")))
  "The face used for comments."
  :group 'agda2-highlight)

(defface agda2-highlight-keyword-face
  '((t (:foreground "DarkOrange3")))
  "The face used for keywords."
  :group 'agda2-highlight)

(defface agda2-highlight-string-face
  '((t (:foreground "firebrick")))
  "The face used for strings."
  :group 'agda2-highlight)

(defface agda2-highlight-number-face
  '((t (:foreground "purple")))
  "The face used for numbers."
  :group 'agda2-highlight)

(defface agda2-highlight-symbol-face
  '((((background light))
     (:foreground "gray25"))
    (((background dark))
     (:foreground "gray75")))
  "The face used for symbols like forall, =, ->, etc."
  :group 'agda2-highlight)

(defface agda2-highlight-primitive-type-face
  '((t (:foreground "medium blue")))
  "The face used for primitive types (like Set and Prop)."
  :group 'agda2-highlight)

(defface agda2-highlight-bound-variable-face
  '((t nil))
  "The face used for bound variables."
  :group 'agda2-highlight)

(defface agda2-highlight-inductive-constructor-face
  '((t (:foreground "green4")))
  "The face used for inductive constructors."
  :group 'agda2-highlight)

(defface agda2-highlight-coinductive-constructor-face
  '((t (:foreground "gold4")))
  "The face used for coinductive constructors."
  :group 'agda2-highlight)

(defface agda2-highlight-datatype-face
  '((t (:foreground "medium blue")))
  "The face used for datatypes."
  :group 'agda2-highlight)

(defface agda2-highlight-field-face
  '((t (:foreground "DeepPink2")))
  "The face used for record fields."
  :group 'agda2-highlight)

(defface agda2-highlight-function-face
  '((t (:foreground "medium blue")))
  "The face used for functions."
  :group 'agda2-highlight)

(defface agda2-highlight-module-face
  '((t (:foreground "purple")))
  "The face used for module names."
  :group 'agda2-highlight)

(defface agda2-highlight-postulate-face
  '((t (:foreground "medium blue")))
  "The face used for postulates."
  :group 'agda2-highlight)

(defface agda2-highlight-primitive-face
  '((t (:foreground "medium blue")))
  "The face used for primitive functions."
  :group 'agda2-highlight)

(defface agda2-highlight-record-face
  '((t (:foreground "medium blue")))
  "The face used for record types."
  :group 'agda2-highlight)

(defface agda2-highlight-dotted-face
  '((t nil))
  "The face used for dotted patterns."
  :group 'agda2-highlight)

(defface agda2-highlight-operator-face
  '((t nil))
  "The face used for operators."
  :group 'agda2-highlight)

(defface agda2-highlight-error-face
  '((t (:foreground "red" :underline t)))
  "The face used for errors."
  :group 'agda2-highlight)

(defface agda2-highlight-unsolved-meta-face
  '((t (:background "yellow"
        :foreground "black")))
  "The face used for unsolved meta variables."
  :group 'agda2-highlight)

(defface agda2-highlight-termination-problem-face
  '((t (:background "light salmon"
        :foreground "black")))
  "The face used for termination problems."
  :group 'agda2-highlight)

(defface agda2-highlight-incomplete-pattern-face
  '((t (:background "wheat"
        :foreground "black")))
  "The face used for incomplete patterns. (Currently unused.)"
  :group 'agda2-highlight)

(defvar agda2-highlight-faces
  '((comment                . agda2-highlight-comment-face)
    (keyword                . agda2-highlight-keyword-face)
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
    (primitive              . agda2-highlight-primitive-face)
    (record                 . agda2-highlight-record-face)
    (dotted                 . agda2-highlight-dotted-face)
    (operator               . agda2-highlight-operator-face)
    (error                  . agda2-highlight-error-face)
    (unsolvedmeta           . agda2-highlight-unsolved-meta-face)
    (terminationproblem     . agda2-highlight-termination-problem-face)
    (incompletepattern      . agda2-highlight-incomplete-pattern-face))
  "Alist mapping code aspects to the face used when displaying them.

The aspects currently recognised are the following:

`bound'                  Bound variables.
`coinductiveconstructor' Coinductive constructors.
`comment'                Comments.
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
`primitive'              Primitive functions.
`primitivetype'          Primitive types (like Set and Prop).
`record'                 Record types.
`string'                 Strings.
`symbol'                 Symbols like forall, =, ->, etc.
`terminationproblem'     Termination problems.
`unsolvedmeta'           Unsolved meta variables.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions

(defun agda2-highlight-reload nil
  "Reload current buffer's syntax information from the syntax file."
  (interactive)
  (let* ((dir (file-name-directory buffer-file-name))
         (name (file-name-nondirectory buffer-file-name))
         (file (concat dir "." name ".el"))
         (inhibit-read-only t))
         ; Ignore read-only status, otherwise this function may fail.
    (annotation-load-file file)))

(defun agda2-highlight-setup nil
  "Set up the `annotation' library for use with `agda2-mode'."
  (font-lock-mode 0)
  (setq annotation-bindings agda2-highlight-faces))

(defun agda2-highlight-clear nil
  "Remove all syntax highlighting added by `agda2-highlight-reload'."
  (interactive)
  (let ((inhibit-read-only t))
       ; Ignore read-only status, otherwise this function may fail.
    (annotation-remove-annotations)))

(defun agda2-highlight-reload-or-clear (&optional arg)
  "Reload syntax highlighting information.
With prefix argument ARG: Remove syntax highlighting."
  (interactive "P")
  (if arg (agda2-highlight-clear)
    (agda2-highlight-reload)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda2-highlight)
;;; agda2-highlight.el ends here
