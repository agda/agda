;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax highlighting for Agda (version ≥ 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'annotation)
(require 'font-lock)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Faces

(defgroup agda2-highlight nil
  "Syntax highlighting for Agda."
  :group 'agda2)

(defface agda2-highlight-comment-face
  '((t (:foreground "firebrick")))
  "*The face used for comments."
  :group 'agda2-highlight)

(defface agda2-highlight-keyword-face
  '((t (:foreground "DarkOrange3")))
  "*The face used for keywords."
  :group 'agda2-highlight)

(defface agda2-highlight-string-face
  '((t (:foreground "firebrick")))
  "*The face used for strings."
  :group 'agda2-highlight)

(defface agda2-highlight-number-face
  '((t (:foreground "purple")))
  "*The face used for numbers."
  :group 'agda2-highlight)

(defface agda2-highlight-symbol-face
  '((t (:foreground "gray25")))
  "*The face used for symbols like forall, =, ->, etc."
  :group 'agda2-highlight)

(defface agda2-highlight-primitive-type-face
  '((t (:foreground "medium blue")))
  "*The face used for primitive types (like Set and Prop)."
  :group 'agda2-highlight)

(defface agda2-highlight-bound-variable-face
  '((t nil))
  "*The face used for bound variables."
  :group 'agda2-highlight)

(defface agda2-highlight-constructor-face
  '((t (:foreground "green4")))
  "The face used for constructors."
  :group 'agda2-highlight)

(defface agda2-highlight-datatype-face
  '((t (:foreground "dark green")))
  "*The face used for datatypes."
  :group 'agda2-highlight)

(defface agda2-highlight-field-face
  '((t (:foreground "DeepPink2")))
  "The face used for record fields."
  :group 'agda2-highlight)

(defface agda2-highlight-function-face
  '((t (:foreground "blue2")))
  "*The face used for functions."
  :group 'agda2-highlight)

(defface agda2-highlight-module-face
  '((t (:foreground "purple")))
  "*The face used for module names."
  :group 'agda2-highlight)

(defface agda2-highlight-postulate-face
  '((t (:foreground "blue4")))
  "The face used for postulates."
  :group 'agda2-highlight)

(defface agda2-highlight-primitive-face
  '((t (:foreground "DodgerBlue1")))
  "The face used for primitive functions."
  :group 'agda2-highlight)

(defface agda2-highlight-record-face
  '((t (:foreground "DeepPink4")))
  "*The face used for record types."
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
  '((t (:foreground "red" :weight bold)))
  "The face used for errors."
  :group 'agda2-highlight)

(defvar agda2-highlight-faces
  ; The faces that are pointers to other faces need to be evaluated,
  ; hence the splices.
  `((comment           . agda2-highlight-comment-face)
    (keyword           . agda2-highlight-keyword-face)
    (string            . agda2-highlight-string-face)
    (number            . agda2-highlight-number-face)
    (symbol            . agda2-highlight-symbol-face)
    (primitivetype     . agda2-highlight-primitive-type-face)
    (bound             . agda2-highlight-bound-variable-face)
    (constructor       . agda2-highlight-constructor-face)
    (datatype          . agda2-highlight-datatype-face)
    (field             . agda2-highlight-field-face)
    (function          . agda2-highlight-function-face)
    (module            . agda2-highlight-module-face)
    (postulate         . agda2-highlight-postulate-face)
    (primitive         . agda2-highlight-primitive-face)
    (record            . agda2-highlight-record-face)
    (dotted            . agda2-highlight-dotted-face)
    (operator          . agda2-highlight-operator-face)
    (error             . agda2-highlight-error-face))
  "An association list mapping from a code aspect to the face used when
displaying the aspect.

The aspects currently recognised are the following:

`bound'             Bound variables.
`comment'           Comments.
`constructor'       Constructors.
`datatype'          Data types.
`dotted'            Dotted patterns.
`error'             Errors.
`field'             Record fields.
`function'          Functions.
`keyword'           Keywords.
`module'            Module names.
`number'            Numbers.
`operator'          Operators.
`postulate'         Postulates.
`primitive'         Primitive functions.
`primitivetype'     Primitive types (like Set and Prop).
`record'            Record types.
`string'            Strings.
`symbol'            Symbols like forall, =, ->, etc.
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions

(defun agda2-highlight-reload nil
  "Reloads syntax information from the syntax file associated with the
current buffer."
  (interactive)
  (let* ((dir (file-name-directory (buffer-file-name)))
         (name (file-name-nondirectory (buffer-file-name)))
         (file (concat dir "." name ".el"))
         )
  (annotation-load-file file)))

(defun agda2-highlight-setup nil
  "Sets up the `annotation' library for use with `agda2-mode'."
  (font-lock-mode 0)
  (setq annotation-bindings agda2-highlight-faces))

(defun agda2-highlight-clear nil
  "Removes all syntax highlighting added by `agda2-highlight-reload'."
  (interactive)
  (annotation-remove-annotations)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda2-highlight)
