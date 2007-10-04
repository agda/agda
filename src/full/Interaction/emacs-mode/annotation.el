;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions for annotating text with faces and help bubbles
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar annotation-bindings nil
  "An association list mapping symbols to faces. Becomes buffer-local
when set.")
(make-variable-buffer-local 'annotation-bindings)

(defvar annotation-goto-map nil
  "A hash table mapping positions to filename/position pairs.
Becomes buffer-local when set.")
(make-variable-buffer-local 'annotation-goto-map)

(defvar annotation-goto-stack nil
  "Keeps track of the positions that `annotation-goto' were invoked
from.")

(defun annotation-goto-possible (pos)
  "Returns t if `annotation-goto-map' has a binding for the buffer
position POS, and nil otherwise."
  (if (gethash pos annotation-goto-map)
      t))

(defun annotation-goto-indirect (pos &optional other-window)
  "Go to the file/position specified by `annotation-goto-map' for the
buffer position POS, if any. If OTHER-WINDOW is t, use another window
to display the given position."
  (let* ((result (gethash pos annotation-goto-map))
         (current-file (buffer-file-name)))
    (if (and (annotation-goto result other-window)
             (not (eq (point) pos)))
        (push `(,current-file . ,pos) annotation-goto-stack))))

(defun annotation-go-back nil
  "Go back to the previous position in which `annotation-goto' was
successfully invoked."
  (when annotation-goto-stack
    (let ((pos (pop annotation-goto-stack)))
      (annotation-goto pos))))

(defun annotation-goto (filepos &optional other-window)
  "Go to file FILE, position POS, if FILEPOS = (FILE . POS), and the
file is readable. Returns t if successful.

If OTHER-WINDOW is t, use another window to display the given
position."
  (when (consp filepos)
    (let ((file (car filepos)))
      (if (file-readable-p file)
          (progn
            (if other-window
                (find-file-other-window file)
              (find-file file))
            (goto-char (cdr filepos))
            t)
        (error "File does not exist or is unreadable: %s." file)))))

(defun annotation-annotate (start end anns &optional info goto)
  "Annotate text between START and END in the current buffer with the
annotations ANNS. All the symbols in ANNS are looked up in
`annotation-bindings', and the face text property for the given
character range is set to the resulting list of faces. If the string
INFO is non-nil, the mouse-face property is set to highlight, and INFO
is used as the help-echo string. If GOTO has the form (filename .
position), then the mouse-face property is set to highlight and, when
the user clicks on the annotated text, then point is warped to the
given position in the given file.

Note that if two faces have the same attribute set, then the first one
takes precedence.

Note also that setting the face text property does not work when
`font-lock-mode' is activated.

All characters whose text properties get set also have the
annotation-annotated property set to t.

Note finally that nothing happens if either START or END are out of
bounds for the current (possibly narrowed) buffer, or END < START."
  (when (and (<= (point-min) start)
             (<= start end)
             (<= end (point-max)))
    (let ((faces (delq nil
                       (mapcar (lambda (ann)
                                 (cdr (assoc ann annotation-bindings)))
                               anns))))
      (when faces
        (add-text-properties start end `(face ,faces)))
      (when info
        (add-text-properties start end
                             `(mouse-face highlight help-echo ,info)))
      (when (consp goto)
        (let ((pos start))
          (while (< pos end)
            (puthash pos goto annotation-goto-map)
            (setq pos (1+ pos))))
        (add-text-properties start end '(mouse-face highlight keymap map)))
      (when (or faces info (consp goto))
        (add-text-properties start end
                             '(annotation-annotated t))))))

(defmacro annotation-preserve-modified-p (&rest code)
  "Runs CODE, making sure to preserve the file modification stamp of
the current buffer."
  `(let ((modp (buffer-modified-p)))
     (unwind-protect
         (progn ,@code)
       (set-buffer-modified-p modp))))

(defmacro annotation-dont-modify-undo-list (&rest code)
  "Runs CODE, but all changes to the undo list are undone after the
call. (Annotating a buffer can add a lot of stuff to the undo list,
and this list has a rather small default maximum size. Furthermore the
text properties added by this library can easily be recomputed.)"
  `(let ((ul buffer-undo-list))
     (unwind-protect
         (progn ,@code)
       (setq buffer-undo-list ul))))

(defmacro annotation-preserve-mod-p-and-undo (&rest code)
  "A combination of `annotation-preserve-modified-p' and
`annotation-dont-modify-undo-list'."
  `(annotation-preserve-modified-p
    (annotation-dont-modify-undo-list ,@code)))

(defun annotation-remove-annotations ()
  "Removes all text properties set by `annotation-annotate' in the
current buffer, and clears `annotation-goto-map'. This function
preserves the file modification stamp of the current buffer and does
not modify the undo list."
  (clrhash annotation-goto-map)
  (annotation-preserve-mod-p-and-undo
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
preserves the file modification stamp of the current buffer and does
not modify the undo list."
  (annotation-preserve-mod-p-and-undo
   ; (make-hash-table) cannot simply be the default value of this
   ; variable, since then the hash table would be shared between
   ; buffers, and this is not a good idea.
   (setq annotation-goto-map (make-hash-table))
   (annotation-remove-annotations)
   (when (file-readable-p file)
     (load-file file))))

(provide 'annotation)
