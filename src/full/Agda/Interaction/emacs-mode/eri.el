;;; eri.el --- Enhanced relative indentation (eri)

;;; Commentary:

;;; Code:

(require 'cl)

(defun eri-current-line-length nil
  "Calculates length of current line."
  (- (line-end-position) (line-beginning-position)))

(defun eri-current-line-empty nil
  "Return non-nil if the current line is empty (not counting white space)."
  (equal (current-indentation)
         (eri-current-line-length)))

(defun eri-maximum (xs)
  "Calculate maximum element in XS.  Return nil if the list is empty."
  (if xs (apply 'max xs)))

(defun eri-take (n xs)
  "Return the first N elements of XS."
  (butlast xs (- (length xs) n)))

(defun eri-split (x xs)
  "Return a pair of lists (XS1 . XS2).
If XS is sorted, then XS = (append XS1 XS2), and all elements in XS1 are <= X,
whereas all elements in XS2 are > X."
  (let* ((pos (or (position-if (lambda (y) (> y x)) xs) (length xs)))
         (xs1 (eri-take pos xs))
         (xs2 (nthcdr pos xs)))
    `(,xs1 . ,xs2)))

(defun eri-calculate-indentation-points-on-line (max)
  "Calculate indentation points on current line.
Only points left of column number MAX are included.
If MAX is nil, then all points are included.  Return points in ascending order.

Example (positions marked with ^ are returned):

  f x y = g 3 (Just y) 5 4
  ^ ^ ^ ^ ^ ^ ^     ^  |
                       |
                       MAX"
  (let ((result))
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
      )))

(defun eri-new-indentation-point ()
  "Calculate a new indentation point, two steps in from the
indentation of the first non-empty line above the current line.
If there is no such line 2 is returned."
  (save-excursion
    (while
        (progn
          (forward-line -1)
          (not (or (bobp)
                   (not (eri-current-line-empty))))))
    (+ 2 (current-indentation))))

(defun eri-calculate-indentation-points (reverse)
  "Calculate some indentation points.  Gives them in reverse order if
REVERSE is non-nil.  See `eri-indent' for a description of how
the indentation points are calculated."
  ;; First find a bunch of indentations used above the current line.
  (let ((points)
        (max))
    (save-excursion
      (while
          (progn
            (forward-line -1)
            ; Skip lines with only white space.
            (unless (eri-current-line-empty)
              (setq points
                    (append
                     (eri-calculate-indentation-points-on-line max)
                     points))
              (setq max (car points)))
            ;; Stop after hitting the beginning of the buffer or a
            ;; non-empty, non-indented line.
            (not (or (bobp)
                     (and (equal (current-indentation) 0)
                          (> (eri-current-line-length) 0)))))))
    ;; Add a new indentation point. Sort the indentations.
    ;; Rearrange the points so that the next point is the one after the
    ;; current one.
    (let* ((ps (add-to-list 'points (eri-new-indentation-point)))
           (ps1 (sort ps '<)) ; Note: sort is destructive.
           (ps2 (eri-split (current-indentation)
                           (remove (current-indentation) ps1))))
      (if reverse
          (append (nreverse (car ps2)) (nreverse (cdr ps2)))
        (append (cdr ps2) (car ps2))))))

(defun eri-indent (&optional reverse)
  "Cycle between some possible indentation points.
With prefix argument REVERSE, cycle in reverse order.

Assume that a file contains the following lines of code, with point on
the line with three dots:

frob = loooooooooooooooooooooooooong identifier
foo = f a b
  where
    f (Foo x) y = let bar = x
                      baz = 3 + 5

...

^ ^ ^ ^    ^  ^ ^ ^   ^ * ^ ^ ^ ^

Then the ^'s and the * mark the indentation points that this function
cycles through.  The indentation points are selected as follows:

  * All lines before the current one, up to and including the first
    non-indented line (or the beginning of the buffer) are considered.

      foo = f a b
        where
          f (Foo x) y = let bar = x
                            baz = 3 + 5

  * On these lines, erase all characters that stand to the right of
    some non-white space character on a lower line.

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

  * The columns of all remaining characters are indentation points.

      f w f (    x  y = l   b   = 3 + 5
      ^ ^ ^ ^    ^  ^ ^ ^   ^   ^ ^ ^ ^

  * A new indentation point is also added, two steps in from the
    indentation of the first non-empty line above the current line
    (or in the second column, if there is no such line).

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
See `eri-indent' for a description of how the indentation points are
calculated."
  (interactive)
  (eri-indent t))

(provide 'eri)
;;; eri.el ends here
