;;; eri.el --- Enhanced relative indentation (eri)

;; SPDX-License-Identifier: MIT License
;; URL: https://github.com/agda/agda
;; Version: 1.0

;;; Commentary:

;; Cycle between indentation points with enhanced relative indentation.

;;; Code:

(defun eri-current-line-length nil
  "Calculate length of current line."
  (- (line-end-position) (line-beginning-position)))

(defun eri-current-line-empty nil
  "Return non-nil if the current line is empty (not counting white space)."
  (= (current-indentation) (eri-current-line-length)))

(defun eri-calculate-indentation-points-on-line (max)
  "Calculate indentation points on current line.
Only points left of column number MAX are included. If MAX is
nil, then all points are included. Points are returned in
ascending order.

Example (positions marked with ^ are returned):

  f x y = g 3 (Just y) 5 4
  ^ ^ ^ ^ ^ ^ ^     ^  |
                       |
                       MAX"
  (let ((result))
    (save-excursion
      (save-restriction
        (beginning-of-line)
        ; To make \\` work in the regexp below:
        (narrow-to-region (line-beginning-position) (line-end-position))
        (while
            (progn
              (let ((pos (and (search-forward-regexp
                               "\\(?:\\s-\\|\\`\\)\\(\\S-\\)" nil t)
                              (match-beginning 1))))
                (when (not (null pos))
                  (let ((pos1 (- pos (line-beginning-position))))
                    (when (or (null max) (< pos1 max))
                      (add-to-list 'result pos1))))
                (and pos
                     (< (point) (line-end-position))
                     (or (null max) (< (current-column) max))))))
        (nreverse result) ; Destructive operation.
        ))))

(defun eri-new-indentation-points ()
  "Calculate new indentation points.
Returns a singleton list containing the column number two steps
in from the indentation of the first non-empty line (white space
excluded) above the current line. If there is no such line,
then the empty list is returned."
  (let ((start (line-beginning-position)))
    (save-excursion
      ; Find a non-empty line above the current one, if any.
      (while
          (progn
            (forward-line -1)
            (not (or (bobp)
                     (not (eri-current-line-empty))))))
      (if (or (= (point) start)
              (eri-current-line-empty))
          nil
        (list (+ 2 (current-indentation)))))))

(defun eri-calculate-indentation-points (reverse)
  "Calculate points used to indent the current line.
The points are given in reverse order if REVERSE is non-nil. See
`eri-indent' for a description of how the indentation points are
calculated; note that the current indentation is not included in
the returned list."
  ;; First find a bunch of indentations used above the current line.
  (let ((points)
        (max)
        (start (line-beginning-position)))
    (save-excursion
      (while
          (progn
            (forward-line -1)
                                        ; Skip the line we started from and lines with nothing but
                                        ; white space.
            (unless (or (= (point) start)
                        (eri-current-line-empty))
              (setq points
                    (append
                     (eri-calculate-indentation-points-on-line max)
                     points))
              (setq max (car points)))
            ;; Stop after hitting the beginning of the buffer or a
            ;; non-empty, non-indented line.
            (not (or (bobp)
                     (and (= (current-indentation) 0)
                          (> (eri-current-line-length) 0)))))))
    ;; Add new indentation points, but remove the current indentation.
    ;; Sort the indentations. Rearrange the points so that the next
    ;; point is the one after the current one. Reverse if necessary.
    ;;
    ;; Note: `sort' and `nreverse' are destructive.
    (let* ((ci (current-indentation))
           (points (sort (remove ci (append (eri-new-indentation-points) points))
                         #'<)))
      (when (< 0 ci (length points))
        (let ((last (last points)) (mid (nthcdr ci points)))
          (setf (nthcdr ci points) nil
                (cdr last) points
                points mid)))
      (if reverse (nreverse points) points))))

(defun eri-indent (&optional reverse)
  "Cycle between some possible indentation points.
With prefix argument REVERSE, cycle in reverse order.

Assume that a file contains the following lines of code, with
point on the line with three dots:

frob = loooooooooooooooooooooooooong identifier
foo = f a b
  where
    f (Foo x) y = let bar = x
                      baz = 3 + 5

...

^ ^ ^ ^    ^  ^ ^ ^   ^ * ^ ^ ^ ^

Then the ^'s and the * mark the indentation points that this
function cycles through. The indentation points are selected as
follows:

  * All lines before the current one, up to and including the
    first non-indented line (or the beginning of the buffer) are
    considered.

      foo = f a b
        where
          f (Foo x) y = let bar = x
                            baz = 3 + 5

  * On these lines, erase all characters that stand to the right
    of some non-white space character on a lower line.

      foo
        whe
          f (Foo x) y = let b
                            baz = 3 + 5

  * Also erase all characters not immediately preceded by white
    space.

      f
        w
          f (    x  y = l   b
                            b   = 3 + 5

  * The columns of all remaining characters are indentation
    points.

      f w f (    x  y = l   b   = 3 + 5
      ^ ^ ^ ^    ^  ^ ^ ^   ^   ^ ^ ^ ^

  * A new indentation point is also added, two steps in from the
    indentation of the first non-empty line (white space
    excluded) above the current line (if there is such a line).

      f w f (    x  y = l   b   = 3 + 5
      ^ ^ ^ ^    ^  ^ ^ ^   ^ * ^ ^ ^ ^"
  (interactive "P")
  (let* ((points (eri-calculate-indentation-points reverse))
         (remaining-points (cdr (member (current-indentation) points)))
         (indentation (if remaining-points
                          (car remaining-points)
                        (car points))))
    (when indentation
      (save-excursion (indent-line-to indentation))
      (if (< (current-column) indentation)
          (indent-line-to indentation)))))

(defun eri-indent-reverse nil
  "Cycle between some possible indentation points (in reverse order).
See `eri-indent' for a description of how the indentation points
are calculated."
  (interactive)
  (eri-indent t))

(provide 'eri)
;;; eri.el ends here
