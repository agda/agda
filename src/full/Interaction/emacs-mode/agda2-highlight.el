;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax highlighting for Agda (version ≥ 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'annotation)
(require 'font-lock)

(defgroup agda2-highlight nil
  "Syntax highlighting for Agda."
  :group 'agda2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; An Agda fontset

(defcustom agda2-highlight-fontset-spec
  "-misc-fixed-medium-r-normal-*-15-*-*-*-*-*-fontset-agda2"
  "The agda2 fontset, which provides the default value for
`agda2-default-face', is created based on this string. Note that
this only works under the X Window System."
  :group 'agda2-highlight
  :type 'string)

(if (eq window-system 'x)
    (create-fontset-from-fontset-spec agda2-highlight-fontset-spec))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Faces

; The default face is used for every character which is not
; highlighted. The other faces all inherit from this face (by
; default). The point of this face is to enable using a dedicated font
; family, with good support for Unicode characters, in Agda buffers
; without forcing this change upon the Emacs user's other buffers.

; Using a fontset/font to specify the face is not really nice, since
; it is not possible to customise the :font field. However, when I
; tried other approaches, including setting the relevant fields
; directly, some characters (mathematical operators) were not
; displayed properly (when the default Emacs font did not support
; them). This method seems to work (at least on the current system). I
; would prefer a solution which was easier to customise, though.

(defface agda2-default-face
  '((t (:font "fontset-agda2")))
  "*The default face used in Agda buffers."
  :group 'agda2-highlight)

(defface agda2-highlight-comment-face
  '((t (:foreground "firebrick" :inherit agda2-default-face)))
  "*The face used for comments."
  :group 'agda2-highlight)

(defface agda2-highlight-keyword-face
  '((t (:foreground "DarkOrange3" :inherit agda2-default-face)))
  "*The face used for keywords."
  :group 'agda2-highlight)

(defface agda2-highlight-string-face
  '((t (:foreground "firebrick" :inherit agda2-default-face)))
  "*The face used for strings."
  :group 'agda2-highlight)

(defface agda2-highlight-number-face
  '((t (:foreground "purple" :inherit agda2-default-face)))
  "*The face used for numbers."
  :group 'agda2-highlight)

(defface agda2-highlight-symbol-face
  '((t (:foreground "gray25" :inherit agda2-default-face)))
  "*The face used for symbols like forall, =, ->, etc."
  :group 'agda2-highlight)

(defface agda2-highlight-primitive-type-face
  '((t (:foreground "medium blue" :inherit agda2-default-face)))
  "*The face used for primitive types (like Set and Prop)."
  :group 'agda2-highlight)

(defface agda2-highlight-bound-variable-face
  '((t (:inherit agda2-default-face)))
  "*The face used for bound variables."
  :group 'agda2-highlight)

(defface agda2-highlight-constructor-face
  '((t (:foreground "green4" :inherit agda2-default-face)))
  "The face used for constructors."
  :group 'agda2-highlight)

(defface agda2-highlight-datatype-face
  '((t (:foreground "dark green" :inherit agda2-default-face)))
  "*The face used for datatypes."
  :group 'agda2-highlight)

(defface agda2-highlight-field-face
  '((t (:foreground "DeepPink2" :inherit agda2-default-face)))
  "The face used for record fields."
  :group 'agda2-highlight)

(defface agda2-highlight-function-face
  '((t (:foreground "blue2" :inherit agda2-default-face)))
  "*The face used for functions."
  :group 'agda2-highlight)

(defface agda2-highlight-module-face
  '((t (:foreground "purple" :inherit agda2-default-face)))
  "*The face used for module names."
  :group 'agda2-highlight)

(defface agda2-highlight-postulate-face
  '((t (:foreground "blue4" :inherit agda2-default-face)))
  "The face used for postulates."
  :group 'agda2-highlight)

(defface agda2-highlight-primitive-face
  '((t (:foreground "DodgerBlue1" :inherit agda2-default-face)))
  "The face used for primitive functions."
  :group 'agda2-highlight)

(defface agda2-highlight-record-face
  '((t (:foreground "DeepPink4" :inherit agda2-default-face)))
  "*The face used for record types."
  :group 'agda2-highlight)

(defface agda2-highlight-dotted-face
  '((t (:inherit agda2-default-face)))
  "The face used for dotted patterns."
  :group 'agda2-highlight)

(defface agda2-highlight-operator-face
  '((t (:inherit agda2-default-face)))
  "The face used for operators."
  :group 'agda2-highlight)

(defface agda2-highlight-error-face
  '((t (:foreground "red" :inherit agda2-default-face)))
  "The face used for errors."
  :group 'agda2-highlight)

(defface agda2-highlight-unsolved-meta-face
  '((t (:background "yellow" :inherit agda2-default-face)))
  "The face used for unsolved meta variables."
  :group 'agda2-highlight)

(defface agda2-highlight-termination-problem-face
  '((t (:background "light salmon" :inherit agda2-default-face)))
  "The face used for termination problems."
  :group 'agda2-highlight)

(defvar agda2-highlight-faces
  ; The faces that are pointers to other faces need to be evaluated,
  ; hence the splices.
  `((comment            . agda2-highlight-comment-face)
    (keyword            . agda2-highlight-keyword-face)
    (string             . agda2-highlight-string-face)
    (number             . agda2-highlight-number-face)
    (symbol             . agda2-highlight-symbol-face)
    (primitivetype      . agda2-highlight-primitive-type-face)
    (bound              . agda2-highlight-bound-variable-face)
    (constructor        . agda2-highlight-constructor-face)
    (datatype           . agda2-highlight-datatype-face)
    (field              . agda2-highlight-field-face)
    (function           . agda2-highlight-function-face)
    (module             . agda2-highlight-module-face)
    (postulate          . agda2-highlight-postulate-face)
    (primitive          . agda2-highlight-primitive-face)
    (record             . agda2-highlight-record-face)
    (dotted             . agda2-highlight-dotted-face)
    (operator           . agda2-highlight-operator-face)
    (error              . agda2-highlight-error-face)
    (unsolvedmeta       . agda2-highlight-unsolved-meta-face)
    (terminationproblem . agda2-highlight-termination-problem-face))
  "An association list mapping from a code aspect to the face used when
displaying the aspect.

The aspects currently recognised are the following:

`bound'              Bound variables.
`comment'            Comments.
`constructor'        Constructors.
`datatype'           Data types.
`dotted'             Dotted patterns.
`error'              Errors.
`field'              Record fields.
`function'           Functions.
`keyword'            Keywords.
`module'             Module names.
`number'             Numbers.
`operator'           Operators.
`postulate'          Postulates.
`primitive'          Primitive functions.
`primitivetype'      Primitive types (like Set and Prop).
`record'             Record types.
`string'             Strings.
`symbol'             Symbols like forall, =, ->, etc.
`terminationproblem' Termination problems.
`unsolvedmeta'       Unsolved meta variables.
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions

(defun agda2-highlight-set-face (face)
  "Sets the `face' text property of every character in the buffer
to FACE. Makes the property front- and rear-sticky."
  (annotation-preserve-mod-p-and-undo
   (add-text-properties (point-min) (point-max)
                        `(face ,face front-sticky t
                                     rear-nonsticky nil))))

(defun agda2-highlight-reload nil
  "Sets the `face' property of all text to `agda2-default-face'
and then reloads syntax information from the syntax file
associated with the current buffer."
  (interactive)
  (agda2-highlight-set-face 'agda2-default-face)
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
  "Removes all syntax highlighting added by
`agda2-highlight-reload'. Sets the `face' property of all text to
`default'."
  (interactive)
  (annotation-remove-annotations)
  (agda2-highlight-set-face 'default)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda2-highlight)
