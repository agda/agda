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

(defcustom agda2-highlight-comment-face
  font-lock-comment-face
  "*The face used for comments."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defcustom agda2-highlight-keyword-face
  font-lock-keyword-face
  "*The face used for keywords."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defcustom agda2-highlight-string-face
  font-lock-string-face
  "*The face used for strings."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defcustom agda2-highlight-number-face
  font-lock-constant-face
  "*The face used for numbers."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defcustom agda2-highlight-bound-variable-face
  font-lock-variable-name-face
  "*The face used for bound variables."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defface agda2-highlight-constructor-face
  '((t (:foreground "green4")))
  "The face used for constructors."
  :group 'agda2-highlight)

(defcustom agda2-highlight-datatype-face
  font-lock-type-face
  "*The face used for datatypes."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defface agda2-highlight-field-face
  '((t (:foreground "HotPink2")))
  "The face used for record fields."
  :group 'agda2-highlight)

(defcustom agda2-highlight-function-face
  font-lock-function-name-face
  "*The face used for functions."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defface agda2-highlight-postulate-face
  '((t (:foreground "dark magenta")))
  "The face used for postulates."
  :group 'agda2-highlight)

(defcustom agda2-highlight-primitive-face
  font-lock-function-name-face
  "The face used for primitive functions."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defcustom agda2-highlight-record-face
  font-lock-type-face
  "*The face used for record types."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defface agda2-highlight-dotted-face
  '((t (:box (:line-width 2 :color "grey75"))))
  "The face used for dotted patterns."
  :group 'agda2-highlight)

(defface agda2-highlight-operator-face
  '((t (:underline t)))
  "The face used for operators."
  :group 'agda2-highlight)

(defcustom agda2-highlight-error-face
  font-lock-warning-face
  "The face used for errors."
  :type 'face
  :require 'font-lock
  :group 'agda2-highlight)

(defvar agda2-highlight-faces
  ; The faces that are pointers to other faces need to be evaluated,
  ; hence the splices.
  `((comment     . ,agda2-highlight-comment-face)
    (keyword     . ,agda2-highlight-keyword-face)
    (string      . ,agda2-highlight-string-face)
    (number      . ,agda2-highlight-number-face)
    (bound       . ,agda2-highlight-bound-variable-face)
    (constructor . agda2-highlight-constructor-face)
    (datatype    . ,agda2-highlight-datatype-face)
    (field       . agda2-highlight-field-face)
    (function    . ,agda2-highlight-function-face)
    (postulate   . agda2-highlight-postulate-face)
    (primitive   . ,agda2-highlight-primitive-face)
    (record      . ,agda2-highlight-record-face)
    (dotted      . agda2-highlight-dotted-face)
    (operator    . agda2-highlight-operator-face)
    (error       . ,agda2-highlight-error-face))
  "An association list mapping from a code aspect to the face used when
displaying the aspect.

The aspects currently recognised are the following:

`bound'       Bound variables.
`comment'     Comments.
`constructor' Constructors.
`datatype'    Data types.
`dotted'      Dotted patterns.
`error'       Errors.
`field'       Record fields.
`function'    Functions.
`keyword'     Keywords.
`number'      Numbers.
`operator'    Operators.
`postulate'   Postulates.
`primitive'   Primitive functions.
`record'      Record types.
`string'      Strings.
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
