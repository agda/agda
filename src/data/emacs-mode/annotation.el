;;; annotation.el --- Functions for annotating text with faces and help bubbles

;; Version: 1.0

;; SPDX-License-Identifier: MIT License
;; URL: https://github.com/agda/agda
;; Version: 1.0

;;; Commentary:

;; Note that this library enumerates buffer positions starting from 1,
;; just like Emacs.

(require 'cl-lib)

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
            (goto-char (cdr filepos))
            t)
        (error "File does not exist or is unreadable: %s." file)))))

(defun annotation-merge-faces (start end faces)
  "Helper procedure used by `annotation-annotate'.
For each position in the range the FACES are merged
with the current value of the annotation-faces text property, and
both the face and the annotation-faces text properties are set to
the resulting list of faces.

Precondition: START and END must be numbers, and START must be
less than END."
  (cl-assert (condition-case nil (< start end) (error nil)))
  (let ((pos start)
        mid)
    (while (< pos end)
      (setq mid (next-single-property-change pos 'annotation-faces
                                             nil end))
      (let* ((old-faces (get-text-property pos 'annotation-faces))
             (all-faces (cl-union old-faces faces)))
        (mapc (lambda (prop) (put-text-property pos mid prop all-faces))
              '(annotation-faces face))
        (setq pos mid)))))

(defun annotation-annotate
    (start end anns &optional token-based info goto)
  "Annotate text between START and END in the current buffer.

Nothing happens if either START or END are out of bounds for the
current (possibly narrowed) buffer, or END <= START.

If ANNS is nil, then those text properties between START and END
that have been set by this function are deleted. Otherwise the
following happens.

All the symbols in ANNS are looked up in `annotation-bindings',
and the resulting list of faces is used to set the face text
property. For each position in the range the faces are merged
with the current value of the annotation-faces text property, and
both the face and the annotation-faces text properties are set to
the resulting list of faces.

If TOKEN-BASED is non-nil, then the annotation-token-based
property is set to t. This means that all text properties set by
`annotation-annotate' in this range are interpreted as being
token-based, including those set by previous calls to this
procedure.

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
  (when (and (<= (point-min) start)
             (< start end)
             (<= end (point-max)))
    (if (null anns)
        (annotation-remove-annotations nil start end)
      (let ((faces (delq nil
                         (mapcar (lambda (ann)
                                   (cdr (assoc ann annotation-bindings)))
                                 anns)))
            (props nil))
        (when faces
          (annotation-merge-faces start end faces)
          (add-to-list 'props 'face)
          (add-to-list 'props 'annotation-faces))
        (when token-based
          (add-text-properties start end
                               `(annotation-token-based t))
          (add-to-list 'props 'annotation-token-based))
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
          (add-to-list 'props 'annotation-annotated)
          (let ((pos start)
                mid)
            (while (< pos end)
              (setq mid (next-single-property-change pos
                           'annotation-annotations nil end))
              (let* ((old-props (get-text-property pos 'annotation-annotations))
                     (all-props (cl-union old-props props)))
                (add-text-properties pos mid
                   `(annotation-annotated t annotation-annotations ,all-props))
                (setq pos mid)))))))))

(defmacro annotation-preserve-mod-p-and-undo (&rest code)
  "Run CODE preserving both the undo data and the modification bit.
Modification hooks are also disabled."
  (declare (debug (&rest form)))
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

(defun annotation-remove-annotations (&optional token-based start end)
  "Remove text properties set by `annotation-annotate'.

In the current buffer. If START and END are given, then
properties are only removed between these positions. If
TOKEN-BASED is non-nil, then only token-based properties are
removed.

This function preserves the file modification stamp of the
current buffer, does not modify the undo list, and temporarily
disables all modification hooks.

Note: This function may fail if there is read-only text in the
buffer."

  ;; remove-text-properties fails for read-only text.

  (annotation-preserve-mod-p-and-undo
   (let ((tag (if token-based
                  'annotation-token-based
                'annotation-annotated))
         (pos (or start (point-min)))
         (end (or end (point-max)))
         pos2)
     (while pos
       (let ((props (get-text-property pos 'annotation-annotations)))
         (setq pos2 (next-single-property-change pos tag nil end))
         (when (and props
                    (or (not token-based)
                        (member 'annotation-token-based props)))
           (remove-text-properties pos (or pos2 (point-max))
              (cl-mapcan (lambda (prop) (list prop nil))
                      (cons 'annotation-annotations props)))))
       (setq pos (unless (or (not pos2) (>= pos2 end)) pos2))))))

(defun annotation-load (goto-help remove &rest cmds)
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

If REMOVE is nil, then old syntax highlighting information is not
removed. Otherwise all token-based syntax highlighting is
removed. In order to reduce the risk of flicker this highlighting
is removed step by step, in conjunction with the addition of new
highlighting. (This process assumes that CMDS is ordered by the
positions of the annotations. If it isn't, then the highlighting
is still applied correctly, but perhaps with more flicker.)

This function preserves the file modification stamp of the
current buffer, does not modify the undo list, and temporarily
disables all modification hooks.

Note: This function may fail if there is read-only text in the
buffer."
  (annotation-preserve-mod-p-and-undo
    (when (listp cmds)
      (let ((pos (point-min)))
        (dolist (cmd cmds)
          (cl-destructuring-bind
              (start end anns &optional token-based info goto) cmd
            (let ((info (if (and (not info) (consp goto))
                            goto-help
                          info)))
              (when remove
                (annotation-remove-annotations
                 'token-based pos end)
                (setq pos end))
              (annotation-annotate
               start end anns token-based info goto))))
        (when remove
          (annotation-remove-annotations
           'token-based pos (point-max)))))))

(provide 'annotation)
;;; annotation.el ends here
