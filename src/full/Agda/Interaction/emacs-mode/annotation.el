;;; annotation.el --- Functions for annotating text with faces and help bubbles

;;; Commentary:
;; 

;;; Code:
(require 'cl)

(defconst annotations-offset (- (save-restriction (widen) (point-min)) 1)
  "Offset between buffer positions and annotations's positions.
Annotations's positions are based on 1, so this adjusts it to the base
position used by your Emacs.")

(defvar annotation-bindings nil
  "An association list mapping symbols to faces.")
(make-variable-buffer-local 'annotation-bindings)

(defvar annotation-goto-stack nil
  "Positions from which `annotation-goto' was invoked.")

(defun annotation-goto-possible (pos)
  "Return t if there's a hyperlink at the buffer position POS, and nil otherwise."
  (if (get-text-property pos 'annotation-goto) t))

(defun annotation-goto-indirect (pos &optional other-window)
  "Follow the `annotation-goto' hyperlink at position POS, if any.
If OTHER-WINDOW is t, use another window to display the given position."
  (let ((previous-file-name buffer-file-name))
    (if (and (annotation-goto (get-text-property pos 'annotation-goto)
                              other-window)
             (not (eq (point) pos)))
        (push `(,previous-file-name . ,pos) annotation-goto-stack))))

(defun annotation-go-back nil
  "Go back to the previous position in which `annotation-goto' was
successfully invoked."
  (when annotation-goto-stack
    (let ((pos (pop annotation-goto-stack)))
      (annotation-goto pos))))

(defun annotation-goto (filepos &optional other-window)
  "Go to file position FILEPOS if the file is readable.
FILEPOS should have the form (FILE . POS).  Return t if successful.

If OTHER-WINDOW is t, use another window to display the given
position."
  (when (consp filepos)
    (let ((file (car filepos)))
      (if (file-readable-p file)
          (progn
            (if other-window
                (find-file-other-window file)
              (find-file file))
            (goto-char (+ (cdr filepos) annotations-offset))
            t)
        (error "File does not exist or is unreadable: %s." file)))))

(defun annotation-annotate (start end anns &optional info goto)
  "Annotate text between START and END in the current buffer.
ANNS are the annotations to apply.
All the symbols in ANNS are looked up in
`annotation-bindings', and the face text property for the given
character range is set to the resulting list of faces.  If the string
INFO is non-nil, the mouse-face property is set to highlight, and INFO
is used as the help-echo string.  If GOTO has the form (FILENAME .
POSITION), then the mouse-face property is set to highlight and, when
the user clicks on the annotated text, then point is warped to the
given position in the given file.

Note that if two faces have the same attribute set, then the first one
takes precedence.

Note also that setting the face text property does not work when
`font-lock-mode' is activated.

All characters whose text properties get set also have the
annotation-annotated property set to t, and
annotation-annotations is set to a list with all the properties
that have been set; this ensures that the text properties can
later be removed (if the annotation-* properties are not tampered
with).

Note finally that nothing happens if either START or END are out of
bounds for the current (possibly narrowed) buffer, or END < START."
  (incf start annotations-offset)
  (incf end annotations-offset)
  (when (and (<= (point-min) start)
             (<= start end)
             (<= end (point-max)))
    (let ((faces (delq nil
                       (mapcar (lambda (ann)
                                 (cdr (assoc ann annotation-bindings)))
                               anns)))
          (props nil))
      (when faces
        (put-text-property start end 'face faces)
        (add-to-list 'props 'face))
      ;; Do this before so `info' can override our default help-echo.
      (when (consp goto)
        (add-text-properties start end
                             `(annotation-goto ,goto
                               mouse-face highlight
                               help-echo "Click mouse-2 to jump to definition"))
        (add-to-list 'props 'annotation-goto)
        (add-to-list 'props 'mouse-face)
        (add-to-list 'props 'help-echo))
      (when info
        (add-text-properties start end
                             `(mouse-face highlight help-echo ,info))
        (add-to-list 'props 'mouse-face)
        (add-to-list 'props 'help-echo))
      (when props
        (add-text-properties start end
                             `(annotation-annotated   t
                               annotation-annotations ,props))))))

(defmacro annotation-preserve-mod-p-and-undo (&rest code)
  "Run CODE preserving both its undo data and modification bit."
  (let ((modp (make-symbol "modp")))
  `(let ((,modp (buffer-modified-p))
         (buffer-undo-list t))
     (unwind-protect
         (progn ,@code)
       ;; FIXME: `restore-buffer-modified-p' would be more efficient.
       (set-buffer-modified-p ,modp)))))

(defun annotation-remove-annotations ()
  "Remove all text properties set by `annotation-annotate' in the current buffer.
This function preserves the file modification stamp of the current buffer
and does not modify the undo list.

Note: This function may fail if there is read-only text in the buffer."

  ;; remove-text-properties fails for read-only text.

  (annotation-preserve-mod-p-and-undo
   (let ((pos (point-min))
         pos2)
     (while pos
       (setq pos2 (next-single-property-change pos 'annotation-annotated))
       (let ((props (get-text-property pos 'annotation-annotations)))
         (when props
           (remove-text-properties pos (or pos2 (point-max))
              (mapcan (lambda (prop) (list prop nil))
                      (append '(annotation-annotated annotation-annotations)
                              props)))))
       (setq pos pos2)))))

(defun annotation-load-file (file)
  "Load and execute FILE, which should contain calls to `annotation-annotate'.
First all existing text properties set by `annotation-annotate'
in the current buffer are removed.  This function preserves the
file modification stamp of the current buffer and does not
modify the undo list.

Note: This function may fail if there is read-only text in the buffer."
  (annotation-preserve-mod-p-and-undo
   (annotation-remove-annotations)
   (when (file-readable-p file)
     ;; FIXME: Giant security hole!!
     ;; (load file nil 'nomessage)
     (let ((cmds (with-temp-buffer
                   (insert "(\n)") (forward-char -2)
                   (insert-file-contents file)
                   (goto-char (point-min))
                   (read (current-buffer)))))
       (dolist (cmd cmds)
         (destructuring-bind (f start end anns &optional info goto) cmd
           (assert (eq f 'annotation-annotate))
           (setq anns (cadr anns))      ;Strip the `quote'.
           (setq goto (cadr goto))      ;Strip the `quote'.
           (annotation-annotate start end anns info goto)))))))

(provide 'annotation)
;;; annotation.el ends here
