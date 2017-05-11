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

(defun annotation-goto-indirect (link &optional other-window)
  "Follow the `annotation-goto' hyperlink pointed to by LINK, if any.

LINK should be a buffer position, or an event object (in which
case the ending position is used).

If the hyperlink exists and the jump is performed successfully,
then `t' is returned, and otherwise `nil' (unless an error is
raised).

If OTHER-WINDOW is non-nil, then another window is used to
display the target position."
  (let (source-pos
        source-window
        source-buffer
        source-file-name
        target)
    (cond ((eventp link)
           (let ((pn (event-end link)))
             (when (not (posn-area pn))
               (setq source-pos (posn-point pn))
               (setq source-window (posn-window pn))
               (setq source-buffer (window-buffer source-window)))))
          ((integerp link)
           (setq source-pos link)
           (setq source-window (selected-window))
           (setq source-buffer (current-buffer)))
          (t (error "Not an integer or event object: %S" link)))
    (when (and source-pos source-buffer)
      (with-current-buffer source-buffer
        (setq target (get-text-property source-pos 'annotation-goto)))
      (when target
        (unless (equal source-window (selected-window))
          (select-window source-window))
        (annotation-goto-and-push source-buffer source-pos target
                                  other-window)))))

(defun annotation-go-back nil
  "Go back to the previous position.
The previous position in which `annotation-goto-and-push' was
successfully invoked."
  (when annotation-goto-stack
    (let ((pos (pop annotation-goto-stack)))
      (annotation-goto pos))))

(defun annotation-goto-and-push (source-buffer source-pos filepos &optional other-window)
  "Like `annotation-goto', but pushes a position when successful.
The position consists of the file visited by SOURCE-BUFFER, and
the position given by SOURCE-POS."
  (let (source-file-name)
    (with-current-buffer source-buffer
      (setq source-file-name buffer-file-name))
    (when (annotation-goto filepos other-window)
      (unless (and (equal source-buffer (current-buffer))
                   (eq source-pos (point)))
        (push `(,source-file-name . ,source-pos)
              annotation-goto-stack))
      t)))

(defun annotation-goto (filepos &optional other-window)
  "Go to file position FILEPOS if the file is readable.
FILEPOS should have the form (FILE . POS).  Return t if successful.

If OTHER-WINDOW is non-nil, use another window to display the
given position."
  (when (consp filepos)
    (let ((file (car filepos)))
      (if (file-readable-p file)
          (progn
            (if other-window
                (find-file-other-window file)
              (find-file file))
            (annotation-goto-position (cdr filepos))
            t)
        (error "File does not exist or is unreadable: %s." file)))))

(defun annotation-goto-position (position)
  "Move point to POSITION."
  (goto-char (+ position annotations-offset)))

(defun annotation-append-text-property (start end prop values)
  "Merges VALUES to text property PROP between START and END."
  (let ((pos start)
        mid)
    (while (< pos end)
      (setq mid (next-single-property-change pos prop nil end))
      (let* ((old-values (get-text-property pos prop))
             (all-values (union old-values values)))
        (put-text-property pos mid prop all-values)
        (setq pos mid)))))

(defun annotation-annotate (start end anns &optional info goto)
  "Annotate text between START and END in the current buffer.

Nothing happens if either START or END are out of bounds for the
current (possibly narrowed) buffer, or END <= START.

If ANNS is nil, then those text properties between START and END
that have been set by this function are deleted. Otherwise the
following happens.

All the symbols in ANNS are looked up in `annotation-bindings',
and the font-lock-face text property for the given character
range is set to the resulting list of faces.

If the string INFO is non-nil, the mouse-face
property is set to highlight, and INFO is used as the help-echo
string. If GOTO has the form (FILENAME . POSITION), then the
mouse-face property is set to highlight, and the given
filename/position will be used by `annotation-goto-indirect' when
it is invoked with a position in the given range.

Note that if a given attribute is defined by several faces, then
the first face's setting takes precedence.

All characters whose text properties get set also have the
annotation-annotated property set to t, and
annotation-annotations is set to a list with all the properties
that have been set; this ensures that the text properties can
later be removed (if the annotation-* properties are not tampered
with)."
  (incf start annotations-offset)
  (incf end annotations-offset)
  (when (and (<= (point-min) start)
             (< start end)
             (<= end (point-max)))
    (if (null anns)
        (annotation-remove-annotations start end)
      (let ((faces (delq nil
                         (mapcar (lambda (ann)
                                   (cdr (assoc ann annotation-bindings)))
                                 anns)))
            (props nil))
        (when faces
          (annotation-append-text-property start end 'font-lock-face faces)
          (add-to-list 'props 'font-lock-face))
        (when (consp goto)
          (add-text-properties start end
                               `(annotation-goto ,goto
                                 mouse-face highlight))
          (add-to-list 'props 'annotation-goto)
          (add-to-list 'props 'mouse-face))
        (when info
          (add-text-properties start end
                               `(mouse-face highlight help-echo ,info))
          (add-to-list 'props 'mouse-face)
          (add-to-list 'props 'help-echo))
        (when props
          (let ((pos start)
                mid)
            (while (< pos end)
              (setq mid (next-single-property-change pos
                           'annotation-annotations nil end))
              (let* ((old-props (get-text-property pos 'annotation-annotations))
                     (all-props (union old-props props)))
                (add-text-properties pos mid
                   `(annotation-annotated t annotation-annotations ,all-props))
                (setq pos mid)))))))))

(defmacro annotation-preserve-mod-p-and-undo (&rest code)
  "Run CODE preserving both the undo data and the modification bit.
Modification hooks are also disabled."
  (let ((modp (make-symbol "modp")))
  `(let ((,modp (buffer-modified-p))
         ;; Don't check if the file is being modified by some other process.
         (buffer-file-name nil)
         ;; Don't record those changes on the undo-log.
         (buffer-undo-list t)
         ;; Don't run modification hooks.
         (inhibit-modification-hooks t))
     (unwind-protect
         (progn ,@code)
       (restore-buffer-modified-p ,modp)))))

(defun annotation-remove-annotations (&optional start end)
  "Remove all text properties set by `annotation-annotate'.

In the current buffer. If START and END are given, then
properties are only removed between these positions.

This function preserves the file modification stamp of the
current buffer, does not modify the undo list, and temporarily
disables all modification hooks.

Note: This function may fail if there is read-only text in the
buffer."

  ;; remove-text-properties fails for read-only text.

  (annotation-preserve-mod-p-and-undo
   (let ((pos (or start (point-min)))
         pos2)
     (while pos
       (setq pos2 (next-single-property-change pos 'annotation-annotated
                                               nil end))
       (let ((props (get-text-property pos 'annotation-annotations)))
         (when props
           (remove-text-properties pos (or pos2 (point-max))
              (mapcan (lambda (prop) (list prop nil))
                      (append '(annotation-annotated annotation-annotations)
                              props)))))
       (setq pos (unless (equal pos2 end) pos2))))))

(defun annotation-load (goto-help &rest cmds)
  "Apply highlighting annotations in CMDS in the current buffer.

The argument CMDS should be a list of lists (start end anns
&optional info goto). Text between start and end will be
annotated with the annotations in the list anns (using
`annotation-annotate'). If info and/or goto are present they will
be used as the corresponding arguments to `annotation-annotate'.

If INFO is nil in a call to `annotation-annotate', and the GOTO
argument is a cons-cell, then the INFO argument is set to
GOTO-HELP. The intention is that the default help text should
inform the user about the \"goto\" facility.

This function preserves the file modification stamp of the
current buffer, does not modify the undo list, and temporarily
disables all modification hooks.

Note: This function may fail if there is read-only text in the
buffer."
  (annotation-preserve-mod-p-and-undo
    (when (listp cmds)
      (dolist (cmd cmds)
        (destructuring-bind (start end anns &optional info goto) cmd
          (let ((info (if (and (not info) (consp goto))
                          goto-help
                        info)))
            (annotation-annotate start end anns info goto)))))))

(provide 'annotation)
;;; annotation.el ends here
