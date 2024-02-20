;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Agda mode code which should run before the first Agda file is
;; loaded
;; SPDX-License-Identifier: MIT License

;;; Code:

;; By adding an `agda2--mark-as-safe' to `defun-declarations-alist', we can use the
;; `declare' syntax at the beginning of a `defun' to denote that the
;; function may be invoked and what form the arguments ought to have.
(eval-and-compile
  (defun agda2--mark-as-safe (fn _args &rest values)
    "Set the `agda2-safe-function' property for the function FN.
VALUES must be a list of `cl-typep'-compatible types that will
each be checked against the arguments when invoked.  This
information is used by `agda2-exec-response' to safeguard the
execution."
    ;; Handle a `&repeat' in the safe argument spec
    (let ((rep (memq '&repeat values)))
      (when rep
        (setf (car rep) (cadr rep)
              (cdr rep) (cddr rep)
              (cdr (last rep)) rep)))
    `(put ',fn 'agda2-safe-function ',values))

  (add-to-list
   'defun-declarations-alist
   (list 'agda2-command #'agda2--mark-as-safe)))

(defvar agda2-directory (file-name-directory load-file-name)
  "Path to the directory that contains agda2.el(c).")

(add-to-list 'load-path (or agda2-directory (car load-path)))

(autoload 'agda2-mode "agda2-mode"
  "Major mode for editing Agda files (version ≥ 2)." t)

;;;###autoload
(add-to-list 'completion-ignored-extensions ".agdai")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.l?agda\\'" . agda2-mode))

;;;###autoload
(add-to-list 'file-coding-system-alist '("\\.l?agda\\'" utf-8 . utf-8))

(provide 'agda2)
