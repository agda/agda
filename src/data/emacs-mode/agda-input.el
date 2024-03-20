;;; -*- lexical-binding: t; -*-
;;; agda-input.el --- The Agda input method

;; SPDX-License-Identifier: MIT License
;;; Commentary:

;; A highly customisable input method which can inherit from other
;; Quail input methods. By default the input method is geared towards
;; the input of mathematical and other symbols in Agda programs.
;;
;; Use M-x customize-group agda-input to customise this input method.
;; Note that the functions defined under "Functions used to tweak
;; translation pairs" below can be used to tweak both the key
;; translations inherited from other input methods as well as the
;; ones added specifically for this one.
;;
;; Use agda-input-show-translations to see all the characters which
;; can be typed using this input method (except for those
;; corresponding to ASCII characters).

;;; Code:

(require 'quail)
(require 'cl-lib)
;; Quail is quite stateful, so be careful when editing this code.  Note
;; that with-temp-buffer is used below whenever buffer-local state is
;; modified.

(require 'json)
;; Agda's extra keybindings are stored in a JSON file
;; (for portability, see github.com/agda/agda/issues/7083)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions

(defun agda-input-concat-map (f xs)
  "Concat (map F XS)."
  (apply 'append (mapcar f xs)))

(defun agda-input-to-string-list (s)
  "Convert a string S to a list of one-character strings, after
removing all space and newline characters."
  (agda-input-concat-map
   (lambda (c) (if (member c (string-to-list " \n"))
              nil
            (list (string c))))
   (string-to-list s)))

(defun agda-input-character-range (from to)
  "A string consisting of the characters from FROM to TO."
  (let (seq)
    (dotimes (i (1+ (- to from)))
      (setq seq (cons (+ from i) seq)))
    (concat (nreverse seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions used to tweak translation pairs

(defun agda-input-compose (f g)
  "λ x -> concatMap F (G x)"
    (lambda (x) (agda-input-concat-map f (funcall g x))))

(defun agda-input-or (f g)
  "λ x -> F x ++ G x"
    (lambda (x) (append (funcall f x) (funcall g x))))

(defun agda-input-nonempty ()
  "Only keep pairs with a non-empty first component."
  (lambda (x) (if (> (length (car x)) 0) (list x))))

(defun agda-input-prepend (prefix)
  "Prepend PREFIX to all key sequences."
    (lambda (x) `((,(concat prefix (car x)) . ,(cdr x)))))

(defun agda-input-prefix (prefix)
  "Only keep pairs whose key sequence starts with PREFIX."
    (lambda (x)
      (if (equal (substring (car x) 0 (length prefix)) prefix)
          (list x))))

(defun agda-input-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX."
    (lambda (x)
      (if (equal (substring (car x)
                            (- (length (car x)) (length suffix)))
                 suffix)
          (list x))))

(defun agda-input-drop (ss)
  "Drop pairs matching one of the given key sequences.
SS should be a list of strings."
    (lambda (x) (unless (member (car x) ss) (list x))))

(defun agda-input-drop-beginning (n)
  "Drop N characters from the beginning of each key sequence."
    (lambda (x) `((,(substring (car x) n) . ,(cdr x)))))

(defun agda-input-drop-end (n)
  "Drop N characters from the end of each key sequence."
    (lambda (x)
      `((,(substring (car x) 0 (- (length (car x)) n)) .
         ,(cdr x)))))

(defun agda-input-drop-prefix (prefix)
  "Only keep pairs whose key sequence starts with PREFIX.
This prefix is dropped."
  (agda-input-compose
   (agda-input-drop-beginning (length prefix))
   (agda-input-prefix prefix)))

(defun agda-input-drop-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX.
This suffix is dropped."
    (agda-input-compose
     (agda-input-drop-end (length suffix))
     (agda-input-suffix suffix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization

;; The :set keyword is set to 'agda-input-incorporate-changed-setting
;; so that the input method gets updated immediately when users
;; customize it. However, the setup functions cannot be run before all
;; variables have been defined. Hence the :initialize keyword is set to
;; 'custom-initialize-default to ensure that the setup is not performed
;; until agda-input-setup is called at the end of this file.

(defgroup agda-input nil
  "The Agda input method.
After tweaking these settings you may want to inspect the resulting
translations using `agda-input-show-translations'."
  :group 'agda2
  :group 'leim)

(defcustom agda-input-tweak-all
  '(agda-input-compose
    (agda-input-prepend "\\")
    (agda-input-nonempty))
  "An expression yielding a function which can be used to tweak
all translations before they are included in the input method.
The resulting function (if non-nil) is applied to every
\(KEY-SEQUENCE . TRANSLATION) pair and should return a list of such
pairs. (Note that the translations can be anything accepted by
`quail-defrule'.)

If you change this setting manually (without using the
customization buffer) you need to call `agda-input-setup' in
order for the change to take effect."
  :group 'agda-input
  :set 'agda-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type 'sexp)

(defcustom agda-input-inherit
  `(("TeX" . (agda-input-compose
              (agda-input-drop '("geq" "leq" "bullet" "qed" "par"))
              (agda-input-or
               (agda-input-drop-prefix "\\")
               (agda-input-or
                (agda-input-compose
                 (agda-input-drop '("^l" "^o" "^r" "^v"))
                 (agda-input-prefix "^"))
                (agda-input-prefix "_")))))
    )
  "A list of Quail input methods whose translations should be
inherited by the Agda input method (with the exception of
translations corresponding to ASCII characters).

The list consists of pairs (qp . tweak), where qp is the name of
a Quail package, and tweak is an expression of the same kind as
`agda-input-tweak-all' which is used to tweak the translation
pairs of the input method.

The inherited translation pairs are added last, after
`agda-input-user-translations' and `agda-input-translations'.

If you change this setting manually (without using the
customization buffer) you need to call `agda-input-setup' in
order for the change to take effect."
  :group 'agda-input
  :set 'agda-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Quail package")
                       (sexp :tag "Tweaking function"))))

(defcustom agda-input-translations
  (let* (
    ;; Support large files
    (max-lisp-eval-depth 2800)
    ;; Set up parser: JSON dictionaries -> LISP lists of (symbol, object) pairs
    (json-object-type 'alist)
    ;; Set up parser: JSON arrays -> LISP lists
    (json-array-type 'list)
    ;; Set up parser: load files relative to this file
    (default-directory (file-name-directory load-file-name))
    (filepath (file-truename "keybindings.json"))
    ;; (_(message "DEBUG: filepath to JSON file=%s" filepath))
    ;; Run the JSON parser
    (parsed (json-read-file filepath))
    ;; (_(message "DEBUG: parsed alist=%S" parsed))
    ;; Concatenate blocks of keybindings into a single list
    (flattened (apply 'append parsed))
    ;; Convert symbol keys to string keys
    ;; (_(message "DEBUG: flattened alist=%S" flattened))
    (reshaped (mapcar (lambda (pair) (cons (symbol-name (car pair)) (cdr pair))) flattened))
    ;; (_(message "DEBUG: alist with stringified keys=%S" reshaped))
    ) ;; in
    reshaped ;; return value
  )
  "A list of translations specific to the Agda input method.
Each element is a pair (KEY-SEQUENCE-STRING . LIST-OF-TRANSLATION-STRINGS).
All the translation strings are possible translations
of the given key sequence; if there is more than one you can choose
between them using the arrow keys.

Note that if you customize this setting you will not
automatically benefit (or suffer) from modifications to its
default value when the library is updated.  If you just want to
add some bindings it is probably a better idea to customize
`agda-input-user-translations'.

These translation pairs are included after those in
`agda-input-user-translations', but before the ones inherited
from other input methods (see `agda-input-inherit').

If you change this setting manually (without using the
customization buffer) you need to call `agda-input-setup' in
order for the change to take effect."
  :group 'agda-input
  :set 'agda-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

(defcustom agda-input-user-translations nil
  "Like `agda-input-translations', but more suitable for user
customizations since by default it is empty.

These translation pairs are included first, before those in
`agda-input-translations' and the ones inherited from other input
methods."
  :group 'agda-input
  :set 'agda-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inspecting and modifying translation maps

(defun agda-input-get-translations (qp)
  "Return a list containing all translations from the Quail
package QP (except for those corresponding to ASCII).
Each pair in the list has the form (KEY-SEQUENCE . TRANSLATION)."
  (with-temp-buffer
    (activate-input-method qp) ; To make sure that the package is loaded.
    (unless (quail-package qp)
      (error "%s is not a Quail package." qp))
    (let ((decode-map (list 'decode-map)))
      (quail-build-decode-map (list (quail-map)) "" decode-map 0)
      (cdr decode-map))))

(defun agda-input-show-translations (qp)
  "Display all translations used by the Quail package QP (a string).
\(Except for those corresponding to ASCII)."
  (interactive (list (read-input-method-name
                      "Quail input method (default %s): " "Agda")))
  (let ((buf (concat "*" qp " input method translations*")))
    (with-output-to-temp-buffer buf
      (with-current-buffer buf
        (quail-insert-decode-map
         (cons 'decode-map (agda-input-get-translations qp)))))))

(defun agda-input-add-translations (trans)
  "Add the given translations TRANS to the Agda input method.
TRANS is a list of pairs (KEY-SEQUENCE . TRANSLATION). The
translations are appended to the current translations."
  (with-temp-buffer
    (dolist (tr (agda-input-concat-map (eval agda-input-tweak-all) trans))
      (quail-defrule (car tr) (cdr tr) "Agda" t))))

(defun agda-input-inherit-package (qp &optional fun)
  "Let the Agda input method inherit the translations from the
Quail package QP (except for those corresponding to ASCII).

The optional function FUN can be used to modify the translations.
It is given a pair (KEY-SEQUENCE . TRANSLATION) and should return
a list of such pairs."
  (let ((trans (agda-input-get-translations qp)))
    (agda-input-add-translations
     (if fun (agda-input-concat-map fun trans)
       trans))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Setting up the input method

(defun agda-input-setup ()
  "Set up the Agda input method based on the customisable
variables and underlying input methods."

  ;; Create (or reset) the input method.
  (with-temp-buffer
    (quail-define-package "Agda" "UTF-8" "∏" t ; guidance
     "Agda input method.
The purpose of this input method is to edit Agda programs, but
since it is highly customisable it can be made useful for other
tasks as well."
     nil nil nil nil nil nil t ; maximum-shortest
     ))

  (agda-input-add-translations
   (mapcar (lambda (tr) (cons (car tr) (vconcat (cdr tr))))
           (append agda-input-user-translations
                   agda-input-translations)))
  (dolist (def agda-input-inherit)
    (agda-input-inherit-package (car def)
                                (eval (cdr def)))))

(defun agda-input-incorporate-changed-setting (sym val)
  "Update the Agda input method based on the customisable
variables and underlying input methods.
Suitable for use in the :set field of `defcustom'."
  (set-default sym val)
  (agda-input-setup))

;; Set up the input method.

(agda-input-setup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda-input)
;;; agda-input.el ends here
