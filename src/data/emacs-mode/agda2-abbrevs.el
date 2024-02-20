;; agda2-abbrevs.el --- Default Agda abbrevs
;; SPDX-License-Identifier: MIT License

;;; Commentary:

;;; Code:

;; Skeletons

(require 'skeleton)

(define-skeleton agda2-abbrevs-module
  "Inserts a module header template."
  nil
  "module " _ " where\n")

(define-skeleton agda2-abbrevs-data
  "Inserts a data template."
  nil
  "data " _ " : Set where\n")

(define-skeleton agda2-abbrevs-record
  "Inserts a record type template."
  nil
  "record " _ " : Set where\n"
  "  field\n")

(define-skeleton agda2-abbrevs-record-value
  "Inserts a record value template."
  nil
  "record {" _ "}")

(define-skeleton agda2-abbrevs-using
  "Inserts a using template."
  nil
  "using (" _ ")")

(define-skeleton agda2-abbrevs-hiding
  "Inserts a hiding template."
  nil
  "hiding (" _ ")")

(define-skeleton agda2-abbrevs-renaming
  "Inserts a renaming template."
  nil
  "renaming (" _ " to " _ ")")

(define-skeleton agda2-abbrevs-forall
  "Inserts a forall template."
  nil
  "∀ {" _ "} ")

(define-skeleton agda2-abbrevs-code-block
  "Inserts a code block."
  nil
  "\\begin{code}\n  " _ "\n\\end{code}\n")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abbrevs

(defvar agda2-abbrevs-defaults '(
  ("m"   "" agda2-abbrevs-module)
  ("d"   "" agda2-abbrevs-data)
  ("c"   "" agda2-abbrevs-code-block)
  ("re"  "" agda2-abbrevs-record)
  ("rec" "" agda2-abbrevs-record-value)
  ("u"   "" agda2-abbrevs-using)
  ("h"   "" agda2-abbrevs-hiding)
  ("r"   "" agda2-abbrevs-renaming)
  ("w"   "where\n")
  ("po"  "postulate")
  ("a"   "abstract\n")
  ("pr"  "private\n")
  ("pu"  "public")
  ("mu"  "mutual\n")
  ("f"   "" agda2-abbrevs-forall)
  ("oi"  "open import "))
  "Abbreviations defined by default in the Agda mode.")

(defcustom agda2-mode-abbrevs-use-defaults nil
  "If non-nil include the default Agda mode abbrevs in `agda2-mode-abbrev-table'.
The abbrevs are designed to be expanded explicitly, so users of `abbrev-mode'
probably do not want to include them.

Restart Emacs in order for this change to take effect."
  :group 'agda2
  :type '(choice (const :tag "Yes" t)
                 (const :tag "No" nil)))

(defvar agda2-mode-abbrev-table nil
  "Agda mode abbrev table.")

(define-abbrev-table
  'agda2-mode-abbrev-table
  (if agda2-mode-abbrevs-use-defaults
      (mapcar (lambda (abbrev)
                (append abbrev
                        (make-list (- 4 (length abbrev)) nil)
                        '((:system t))))
              agda2-abbrevs-defaults)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda2-abbrevs)
;;; agda2-abbrevs.el ends here
