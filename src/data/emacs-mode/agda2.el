;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Agda mode code which should run before the first Agda file is
;; loaded

(defvar agda2-directory (file-name-directory load-file-name)
  "Path to the directory that contains agda2.el(c).")

(add-to-list 'load-path (or agda2-directory (car load-path)))

(autoload 'agda2-mode "agda2-mode"
  "Major mode for editing Agda files (version ≥ 2)." t)
(add-to-list 'auto-mode-alist '("\\.\\(l?agda\\|lagda\\.\\(tex\\|rst\\|md\\)\\)\\'" . agda2-mode))
(modify-coding-system-alist 'file "\\.\\(l?agda\\|lagda\\.\\(tex\\|rst\\|md\\)\\)\\'" 'utf-8)

(provide 'agda2)
