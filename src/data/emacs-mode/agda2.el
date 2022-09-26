;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Agda mode code which should run before the first Agda file is
;; loaded
;; SPDX-License-Identifier: MIT License

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
