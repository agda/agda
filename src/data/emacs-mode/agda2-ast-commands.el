;;; agda2-ast-commands.el --- Use AST selections with goal-only commands -*- lexical-binding: t; -*-
;; Copyright (c) 2025
;; SPDX-License-Identifier: MIT
;;
;; Drop this file somewhere on your `load-path` and:
;;   (require 'agda2-ast-commands)
;; Optionally also add in your init (or agda2.el):
;;   (with-eval-after-load 'agda2-mode
;;     (require 'agda2-ast-commands))
;;
;; This enables a tiny minor mode which, when active, allows commands that usually
;; require point to be inside a goal to also work when an AST node is selected
;; (from agda2-ast.el). In that case we send the command with interaction id = -1
;; and the node's buffer range.
;;
;; Robustness tweaks in this version:
;;  - Install advices ONCE and guard them by the minor mode so they do not flap.
;;  - Intercept agda2-goal-cmd (for goal-only commands) and all the existing
;;    *-maybe-toplevel entry points which have a goal variant:
;;      * agda2-infer-type-maybe-toplevel
;;      * agda2-compute-normalised-maybe-toplevel
;;      * agda2-module-contents-maybe-toplevel
;;      * agda2-why-in-scope-maybe-toplevel
;;  - Also intercept agda2-infer-type-.*toplevel variants discovered at
;;    runtime, so we catch different Agda versions.
;;  - Ensure advices are installed both when this file is required before and
;;    after agda2-mode loads.
;;
;; Assumes: agda2-mode functions (agda2-go, agda2-mkRange, agda2-string-quote,
;;          agda2-goal-at), and the selection/state of agda2-ast.el.

(require 'cl-lib)
(require 'agda2-ast nil t)

;; Silence byte-compiler about external functions.
(declare-function agda2-go "agda2-mode" (&rest args))
(declare-function agda2-goal-at "agda2-mode" (pos))
(declare-function agda2-mkRange "agda2-mode" (range))
(declare-function agda2-string-quote "agda2-mode" (s))

(defgroup agda2-ast-commands nil
  "Bridge: let goal-only commands act on the current AST node selection."
  :group 'agda2)

(defun agda2-ast-commands--active-p ()
  "Non-nil when the advice should act in the current buffer."
  (and (derived-mode-p 'agda2-mode)
       (bound-and-true-p agda2-ast-commands-mode)))

(defun agda2-ast-commands--selected-range ()
  "Return (BEG . END) for the currently selected AST node, or nil."
  (when (and (boundp 'agda2-ast--current) agda2-ast--current
             (fboundp 'agda2-ast--to-buffer-pos))
    (agda2-ast--to-buffer-pos agda2-ast--current)))

(defun agda2-ast-commands--around-goal-cmd (orig-fun cmd save &optional want ask &rest args)
  "Advice around agda2-goal-cmd.
If point is not in a goal but an AST node is selected, send CMD with
interaction id = -1 and the node's range; otherwise call ORIG-FUN."
  (if (not (agda2-ast-commands--active-p))
      (apply orig-fun cmd save want ask args)
    (if (agda2-goal-at (point))
        (apply orig-fun cmd save want ask args)
      (let ((r (agda2-ast-commands--selected-range)))
        (if (consp r)
            (let* ((beg (car r))
                   (end (cdr r))
                   (node-text (buffer-substring-no-properties beg end))
                   (blankp (string-match "\\`\\s-*\\'" node-text))
                   (range-str (agda2-mkRange (list beg end)))
                   (input-str
                    (cond
                     ;; No input expected.
                     ((null want) "")
                     ;; Treat WANT = 'goal as “use the node text”.
                     ((eq want 'goal) node-text)
                     ;; WANT is a prompt string: mirror agda2-goal-cmd semantics.
                     ((stringp want)
                      (if (or ask blankp)
                          (read-string (concat want ": ") nil nil node-text t)
                        node-text))
                     ;; Fallback.
                     (t ""))))
              (apply #'agda2-go save t 'busy t
                     cmd "-1" range-str (agda2-string-quote input-str) args))
          (user-error
           "This command can be used from within a goal, or with an AST node selected."))))))

(defun agda2-ast-commands--around-infer-maybe-toplevel (orig-fun &rest args)
  "Advice around agda2-infer-type-maybe-toplevel.
If outside a goal but an AST node is selected, behave like the goal variant."
  (if (not (agda2-ast-commands--active-p))
      (apply orig-fun args)
    (if (agda2-goal-at (point))
        (apply orig-fun args)
      (let ((r (agda2-ast-commands--selected-range)))
        (if (consp r)
            (let ((current-prefix-arg current-prefix-arg))
              (call-interactively 'agda2-infer-type))
          (apply orig-fun args))))))

(defun agda2-ast-commands--around-compute-maybe-toplevel (orig-fun &rest args)
  "Advice around agda2-compute-normalised-maybe-toplevel.
If outside a goal but an AST node is selected, behave like the goal variant."
  (if (not (agda2-ast-commands--active-p))
      (apply orig-fun args)
    (if (agda2-goal-at (point))
        (apply orig-fun args)
      (let ((r (agda2-ast-commands--selected-range)))
        (if (consp r)
            (let ((current-prefix-arg current-prefix-arg))
              (call-interactively 'agda2-compute-normalised))
          (apply orig-fun args))))))

(defun agda2-ast-commands--around-module-contents-maybe-toplevel (orig-fun &rest args)
  "Advice around agda2-module-contents-maybe-toplevel.
If outside a goal but an AST node is selected, behave like the goal variant."
  (if (not (agda2-ast-commands--active-p))
      (apply orig-fun args)
    (if (agda2-goal-at (point))
        (apply orig-fun args)
      (let ((r (agda2-ast-commands--selected-range)))
        (if (consp r)
            (let ((current-prefix-arg current-prefix-arg))
              (call-interactively 'agda2-module-contents))
          (apply orig-fun args))))))

(defun agda2-ast-commands--around-why-in-scope-maybe-toplevel (orig-fun &rest args)
  "Advice around agda2-why-in-scope-maybe-toplevel.
If outside a goal but an AST node is selected, behave like the goal variant."
  (if (not (agda2-ast-commands--active-p))
      (apply orig-fun args)
    (if (agda2-goal-at (point))
        (apply orig-fun args)
      (let ((r (agda2-ast-commands--selected-range)))
        (if (consp r)
            (let ((current-prefix-arg current-prefix-arg))
              (call-interactively 'agda2-why-in-scope))
          (apply orig-fun args))))))

(defun agda2-ast-commands--around-infer-toplevel (orig-fun &rest args)
  "Advice around agda2-infer-type-.*toplevel variants.
If an AST node is selected (and we are not in a goal) redirect to the goal
variant agda2-infer-type."
  (if (not (agda2-ast-commands--active-p))
      (apply orig-fun args)
    (let ((r (agda2-ast-commands--selected-range)))
      (if (and (not (agda2-goal-at (point))) (consp r))
          (let ((current-prefix-arg current-prefix-arg))
            (call-interactively 'agda2-infer-type))
        (apply orig-fun args)))))

(defun agda2-ast-commands--advice-infer-toplevel-variants ()
  "Advise all visible agda2-infer-type-.*toplevel function variants."
  (mapatoms
   (lambda (sym)
     (let ((name (and (symbolp sym) (symbol-name sym))))
       (when (and name
                  (string-match-p "\\`agda2-infer-type-.*toplevel\\'" name)
                  (fboundp sym)
                  (not (advice-member-p #'agda2-ast-commands--around-infer-toplevel sym)))
         (advice-add sym :around #'agda2-ast-commands--around-infer-toplevel))))))

(defun agda2-ast-commands--install-advices ()
  "Install advices; safe to call multiple times."
  (condition-case err
      (progn
        ;; goal-cmd: always present in agda2-mode.
        (unless (advice-member-p #'agda2-ast-commands--around-goal-cmd 'agda2-goal-cmd)
          (advice-add 'agda2-goal-cmd :around #'agda2-ast-commands--around-goal-cmd))
        ;; infer-type maybe-toplevel (if present in this Agda version).
        (when (and (fboundp 'agda2-infer-type-maybe-toplevel)
                   (not (advice-member-p
                         #'agda2-ast-commands--around-infer-maybe-toplevel
                         'agda2-infer-type-maybe-toplevel)))
          (advice-add 'agda2-infer-type-maybe-toplevel :around
                      #'agda2-ast-commands--around-infer-maybe-toplevel))
        ;; compute-normalised maybe-toplevel (if present).
        (when (and (fboundp 'agda2-compute-normalised-maybe-toplevel)
                   (not (advice-member-p
                         #'agda2-ast-commands--around-compute-maybe-toplevel
                         'agda2-compute-normalised-maybe-toplevel)))
          (advice-add 'agda2-compute-normalised-maybe-toplevel :around
                      #'agda2-ast-commands--around-compute-maybe-toplevel))
        ;; module-contents maybe-toplevel (if present).
        (when (and (fboundp 'agda2-module-contents-maybe-toplevel)
                   (not (advice-member-p
                         #'agda2-ast-commands--around-module-contents-maybe-toplevel
                         'agda2-module-contents-maybe-toplevel)))
          (advice-add 'agda2-module-contents-maybe-toplevel :around
                      #'agda2-ast-commands--around-module-contents-maybe-toplevel))
        ;; why-in-scope maybe-toplevel (if present).
        (when (and (fboundp 'agda2-why-in-scope-maybe-toplevel)
                   (not (advice-member-p
                         #'agda2-ast-commands--around-why-in-scope-maybe-toplevel
                         'agda2-why-in-scope-maybe-toplevel)))
          (advice-add 'agda2-why-in-scope-maybe-toplevel :around
                      #'agda2-ast-commands--around-why-in-scope-maybe-toplevel))
        ;; capture infer-type toplevel variants that exist now.
        (agda2-ast-commands--advice-infer-toplevel-variants))
    (error
     (message "agda2-ast-commands: advice installation error: %S" err))))

;;;###autoload
(define-minor-mode agda2-ast-commands-mode
  "Enable goal-only commands to operate on a selected AST node (from agda2-ast.el).
When enabled,
 - If point is inside a goal, commands behave exactly as before.
 - If point is not inside a goal but an AST node is selected (via agda2-ast),
   we send the command with interaction id = -1 and the node's range.
 - Otherwise, we show a friendly message explaining how to use the command."
  :lighter " ◇AST→Cmd")

;;;###autoload
(defun agda2-ast-commands-enable-by-default ()
  "Enable agda2-ast-commands-mode automatically in agda2-mode buffers."
  (add-hook 'agda2-mode-hook #'agda2-ast-commands-mode))

;; Enable by default.
(agda2-ast-commands-enable-by-default)

;; Install advices both now (if agda2-mode is already loaded) and after it loads.
(when (featurep 'agda2-mode)
  (agda2-ast-commands--install-advices))

(with-eval-after-load 'agda2-mode
  ;; Run once and also discover any toplevel variants defined late.
  (agda2-ast-commands--install-advices)
  (agda2-ast-commands--advice-infer-toplevel-variants))

(provide 'agda2-ast-commands)
;;; agda2-ast-commands.el ends here
