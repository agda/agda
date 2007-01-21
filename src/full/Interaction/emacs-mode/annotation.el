;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for annotating text with faces and help bubbles
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar annotation-bindings nil
  "An association list mapping symbols to faces. Becomes buffer-local
when set.")
(make-variable-buffer-local 'annotation-bindings)

(defun annotation-annotate (start end anns &optional info)
  "Annotate text between START and END in the current buffer with the
annotations ANNS. All the symbols in ANNS are looked up in
`annotation-bindings', and the face text property for the given
character range is set to the resulting list of faces. If the string
INFO is non-nil, the mouse-face property is set to highlight, and INFO
is used as the help-echo string.

Note that if two faces have the same attribute set, then the first one
takes precedence.

Note also that setting the face text property does not work when
`font-lock-mode' is activated.

All characters whose text properties get set also have the
rear-nonsticky and annotation-annotated properties set to t."
  (let ((faces (delq nil
                     (mapcar (lambda (ann)
                               (cdr (assoc ann annotation-bindings)))
                             anns))))
    (when faces
        (add-text-properties start end `(face ,faces)))
    (when info
      (add-text-properties start end
                           `(mouse-face highlight help-echo ,info)))
    (when (or faces info)
      (add-text-properties start end
                           '(annotation-annotated t rear-nonsticky t)))))

(defmacro annotation-preserve-modified-p (&rest code)
  "Runs CODE, making sure to preserve the file modification stamp of
the current buffer."
  `(let ((modp (buffer-modified-p)))
     ,@code
     (set-buffer-modified-p modp)))

(defun annotation-remove-annotations ()
  "Removes all text properties set by `annotation-annotate' in the
current buffer. This function preserves the file modification stamp of
the current buffer."
  (annotation-preserve-modified-p
   (let ((pos (point-min))
         pos2
         pos3)
     (while pos
       (setq pos2 (next-single-property-change pos 'annotation-annotated))
       (setq pos3 (or pos2 (point-max)))
       (when (get-text-property pos 'annotation-annotated)
         (remove-text-properties pos pos3
                                 '(annotation-annotated nil
                                   rear-nonsticky nil
                                   mouse-face nil
                                   help-echo nil
                                   face nil)))
       (setq pos pos2)))))

(defun annotation-load-file (file)
  "Loads and executes file FILE, which is assumed to contain calls to
`annotation-annotate'. First all existing text properties set by
`annotation-annotate' in the current buffer are removed. This function
preserves the file modification stamp of the current buffer."
  (annotation-preserve-modified-p
   (annotation-remove-annotations)
   (when (file-readable-p file)
     (load-file file))))

(provide 'annotation)
