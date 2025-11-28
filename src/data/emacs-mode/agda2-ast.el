;;; agda2-ast.el --- AST-aware navigation for Agda buffers -*- lexical-binding: t; -*-

;; Minimal v1: cache the whole AST map per buffer and navigate locally.
;; Assumptions: UTF-8; POSITIONS = 'codepoint (preferred) or 'line-col.

(require 'cl-lib)

;;;; Customization

(defgroup agda2-ast nil
  "AST-aware navigation for Agda."
  :group 'agda2)

(defface agda2-ast-selection-face
  '((t :inherit region :extend t))
  "Face used to visualize the current AST node selection."
  :group 'agda2-ast)

(defface agda2-ast-children-face
  '((t :inherit secondary-selection :extend t))
  "Face used to visualize the immediate children of the current AST node."
  :group 'agda2-ast)

(custom-set-faces
 ;; children (immediate descendants)
 '(agda2-ast-children-face ((t :background "#79acba" :extend t)))
 ;; current node (primary selection)
 '(agda2-ast-selection-face ((t :background "#b8f0ff" :extend t))))

(defcustom agda2-ast-auto-enable t
  "Enable `agda2-ast-navigation-mode' automatically when a map arrives."
  :type 'boolean
  :group 'agda2-ast)


;; Optional knobs for child-highlighting behavior and overlay precedence.
(defcustom agda2-ast-highlight-children t
  "When non-nil, highlight the immediate children of the selected node."
  :type 'boolean
  :group 'agda2-ast)

(defcustom agda2-ast-selection-priority 100
  "Overlay priority for the main selection overlay."
  :type 'integer
  :group 'agda2-ast)

(defcustom agda2-ast-children-priority 110
  "Overlay priority for overlays that highlight the children."
  :type 'integer
  :group 'agda2-ast)


;;;; Buffer-local state

(defvar-local agda2-ast--positions 'codepoint) ; 'codepoint | 'line-col
(defvar-local agda2-ast--tops     nil)         ; list of root node ids
(defvar-local agda2-ast--nodes    nil)         ; id -> plist (:kind :beg :end :children)
(defvar-local agda2-ast--parents  nil)         ; id -> parent-id (or nil)
(defvar-local agda2-ast--by-start nil)         ; vector of ids, sorted by start pos
(defvar-local agda2-ast--current  nil)         ; current node id
(defvar-local agda2-ast--overlay  nil)         ; single visualization overlay
(defvar-local agda2-ast--child-overlays nil)   ; overlays for immediate children
(defvar-local agda2-ast--tick     0)           ; modified tick at ingest

;;;; Small utils

(defun agda2-ast--ensure-overlay ()
  (or agda2-ast--overlay
      (let ((ov (make-overlay (point-min) (point-min) nil t t)))
        (overlay-put ov 'priority agda2-ast-selection-priority)
        (setq agda2-ast--overlay ov))))

(defun agda2-ast--clear-child-overlays ()
  "Delete any existing overlays used to highlight children."
  (when agda2-ast--child-overlays
    (mapc (lambda (ov) (when (overlayp ov) (delete-overlay ov)))
          agda2-ast--child-overlays)
    (setq agda2-ast--child-overlays nil)))

(defun agda2-ast--update-children-highlights (id)
  "Place overlays over immediate children of ID."
  (agda2-ast--clear-child-overlays)
  (when (and agda2-ast-highlight-children id)
    (dolist (k (agda2-ast--children id))
      (let* ((pr (agda2-ast--to-buffer-pos k))
             (b  (car pr))
             (e  (cdr pr))
             (ov (make-overlay b e nil t t)))
        (overlay-put ov 'face 'agda2-ast-children-face)
        (overlay-put ov 'priority agda2-ast-children-priority)
        (overlay-put ov 'evaporate t)
        (push ov agda2-ast--child-overlays)))))

(defun agda2-ast--msg (fmt &rest args)
  (apply #'message (concat "[AST] " fmt) args))

(defun agda2-ast--plist (id)
  (and (hash-table-p agda2-ast--nodes) (gethash id agda2-ast--nodes)))

(defun agda2-ast--children (id)
  (plist-get (agda2-ast--plist id) :children))

(defun agda2-ast--parent (id)
  (and (hash-table-p agda2-ast--parents) (gethash id agda2-ast--parents)))

(defun agda2-ast--range (id)
  (let* ((pl (agda2-ast--plist id))
         (b  (plist-get pl :beg))
         (e  (plist-get pl :end)))
    (cons b e)))

(defun agda2-ast--beg (id) (car (agda2-ast--range id)))
(defun agda2-ast--end (id) (cdr (agda2-ast--range id)))

(defun agda2-ast--pos-from-offset (off)
  "Treat OFF as a 1-based Emacs character position; clamp."
  (max (point-min) (min off (point-max))))

(defun agda2-ast--pos-from-line-col (line col)
  (save-excursion
    (goto-char (point-min))
    (forward-line (1- (max 1 line))) ; line is 1-based
    (move-to-column (1- (max 1 col))) ; column is 1-based -> 0-based for move-to-column
    (point)))

(defun agda2-ast--lc->pos (lc)
  "Convert a line/col value LC into a buffer position.
LC may be a dotted pair (LINE . COL), a 2-list (LINE COL), a
2-vector #(LINE COL), or a plain number (treated as an offset)."
  (cond
   ;; (LINE . COL)
   ((consp lc)
    (agda2-ast--pos-from-line-col (car lc) (cdr lc)))
   ;; (LINE COL)
   ((and (listp lc) (= (length lc) 2))
    (agda2-ast--pos-from-line-col (nth 0 lc) (nth 1 lc)))
   ;; #(LINE COL)
   ((and (vectorp lc) (= (length lc) 2))
    (agda2-ast--pos-from-line-col (aref lc 0) (aref lc 1)))
   ;; Fallback: treat as codepoint offset if numeric
   ((numberp lc)
    (agda2-ast--pos-from-offset lc))
   (t
    (error "Unsupported line/col value: %S" lc))))

(defun agda2-ast--to-buffer-pos (n)
  "Return (BEG . END) buffer positions for node id N."
  (pcase agda2-ast--positions
    ('codepoint
     (let* ((b (agda2-ast--beg n))
            (e (agda2-ast--end n)))
       (cons (agda2-ast--pos-from-offset b)
             (agda2-ast--pos-from-offset e))))
    ('line-col
     (let* ((b (agda2-ast--beg n))
            (e (agda2-ast--end n)))
       (cons (agda2-ast--lc->pos b)
             (agda2-ast--lc->pos e))))
    (_
     (error "Unknown positions kind: %S" agda2-ast--positions))))

(defun agda2-ast--select (id &optional echo)
  "Select node ID: move visualization overlay, optionally echo kind.
This does *not* move point; navigation commands decide whether to
move point themselves."
  (setq agda2-ast--current id)
  (let* ((range (agda2-ast--to-buffer-pos id))
         (b (car range)) (e (cdr range)))
    (agda2-ast--ensure-overlay)
    (move-overlay agda2-ast--overlay b e)
    (overlay-put agda2-ast--overlay 'face 'agda2-ast-selection-face)
    (overlay-put agda2-ast--overlay 'priority agda2-ast-selection-priority)
    ;; Draw the immediate children on top of the current selection.
    (agda2-ast--update-children-highlights id)
    (when echo
      (agda2-ast--msg "%s"
                       (or (plist-get (agda2-ast--plist id) :kind) "node")))))

(defun agda2-ast--stale-p ()
  (/= agda2-ast--tick (buffer-chars-modified-tick)))

;;;; Ingest the map sent by Agda

(defun agda2-ast--ingest (positions tops nodes)
  "Cache the AST map locally.
POSITIONS is \\='codepoint or \\='line-col.
TOPS is a list of root ids.
NODES is a list of (ID KIND BEG END (CHILD ...))."
  (let* ((nodes-ht   (make-hash-table :test #'eql :size (max 64 (* 2 (length nodes)))))
         (parents-ht (make-hash-table :test #'eql :size (max 64 (* 2 (length nodes))))))
    ;; Insert nodes, compute parents as we go.
    (dolist (n nodes)
      (when (and (consp n) (>= (length n) 5))
        (let ((id   (nth 0 n))
              (kind (nth 1 n))
              (beg  (nth 2 n))
              (end  (nth 3 n))
              (kids (nth 4 n)))
          (puthash id (list :id id :kind kind :beg beg :end end :children kids) nodes-ht)
          (dolist (k kids) (puthash k id parents-ht)))))
    ;; Save core state first (so helpers can use it)
    (setq agda2-ast--positions positions
          agda2-ast--tops      tops
          agda2-ast--nodes     nodes-ht
          agda2-ast--parents   parents-ht
          agda2-ast--tick      (buffer-chars-modified-tick))
    ;; Build sorted index by actual buffer start positions
    (let ((triples '()))
      (maphash
       (lambda (id _pl)
         (let* ((pr (agda2-ast--to-buffer-pos id))
                (b (car pr)) (e (cdr pr)))
           (push (list id b e) triples)))
       nodes-ht)
      (setq triples
            (sort triples
                  (lambda (a b)
                    (let ((ba (nth 1 a)) (ea (nth 2 a))
                          (bb (nth 1 b)) (eb (nth 2 b)))
                      (or (< ba bb) (and (= ba bb) (> ea eb)))))))
      (setq agda2-ast--by-start
            (vconcat (mapcar #'car triples))))
    ;; Auto-enable and select at point
    (when agda2-ast-auto-enable
      (agda2-ast-navigation-mode 1))
    (agda2-ast-select-at-point)))

;;;; Node lookup

(defun agda2-ast--node-at-pos (pos)
  "Return the *smallest* node covering POS, or nil."
  (when (and (vectorp agda2-ast--by-start)
             (> (length agda2-ast--by-start) 0))
    (let* ((vec agda2-ast--by-start)
           (lo 0) (hi (1- (length vec))) (best -1))
      ;; binary search: last id with beg <= pos
      (while (<= lo hi)
        (let* ((mid (ash (+ lo hi) -1))
               (id  (aref vec mid))
               (pr  (agda2-ast--to-buffer-pos id))
               (b   (car pr)))
          (if (<= b pos)
              (progn
                (setq best mid)
                (setq lo (1+ mid)))
            (setq hi (1- mid)))))
      (when (>= best 0)
        ;; walk backwards; pick the smallest node that contains pos
        (let ((k best) (found-id nil) (found-len nil))
          (while (>= k 0)
            (let* ((id  (aref vec k))
                   (pr  (agda2-ast--to-buffer-pos id))
                   (b   (car pr))
                   (e   (cdr pr)))
              (if (<= b pos)
                  (progn
                    (when (< pos e)
                      (let ((len (- e b)))
                        (when (or (null found-len) (< len found-len))
                          (setq found-id id
                                found-len len))))
                    (setq k (1- k)))
                (setq k -1))))
          found-id)))))

;;;; Navigation helpers that take point into account

(defun agda2-ast--pos-inside-node-p (pos id)
  "Return non-nil iff POS lies inside the buffer range of node ID."
  (when id
    (let* ((range (agda2-ast--to-buffer-pos id))
           (b (car range))
           (e (cdr range)))
      (and (<= b pos) (< pos e)))))

(defun agda2-ast--ensure-current-at-point ()
  "Ensure `agda2-ast--current' is the smallest node at point.
If no node is currently selected, or point is outside the current
node, select the smallest node under point and return non-nil.
Otherwise, do nothing and return nil."
  (let* ((pos (point)))
    (cond
     ;; No current node: snap to node at point, if any.
     ((null agda2-ast--current)
      (let ((id (agda2-ast--node-at-pos pos)))
        (if id
            (progn
              (agda2-ast--select id t)
              t)
          (agda2-ast--msg "No node at point.")
          t)))                     ; we handled the command (even if by error)
     ;; Current node doesn't contain point: re-snap to node at point.
     ((not (agda2-ast--pos-inside-node-p pos agda2-ast--current))
      (let ((id (agda2-ast--node-at-pos pos)))
        (if id
            (progn
              (agda2-ast--select id t)
              t)
          (agda2-ast--msg "No node at point.")
          t)))
     ;; Current node already matches point: nothing to do.
     (t nil))))

(defun agda2-ast--child-containing-pos (parent-id pos)
  "Return child of PARENT-ID whose range contains POS, or nil."
  (let ((kids (agda2-ast--children parent-id))
        (best nil)
        (best-len nil))
    (dolist (k kids)
      (let* ((pr (agda2-ast--to-buffer-pos k))
             (b (car pr))
             (e (cdr pr)))
        (when (and (<= b pos) (< pos e))
          (let ((len (- e b)))
            (when (or (null best-len) (< len best-len))
              (setq best k
                    best-len len))))))
    best))

;;;; Public interactive commands

(defun agda2-ast-select-at-point ()
  "Select the smallest node covering point (or region start)."
  (interactive)
  (if (agda2-ast--stale-p)
      (agda2-ast--msg "AST map is stale; reload (C-c C-l) to refresh.")
    (let* ((pos (if (use-region-p) (region-beginning) (point)))
           (id  (agda2-ast--node-at-pos pos)))
      (if id
          (agda2-ast--select id t)
        (agda2-ast--msg "No node at point.")))))

(defun agda2-ast-up ()
  "Select parent of the current node, without moving point.
If no node is yet selected or point lies outside the selected
node, first select the smallest node at point."
  (interactive)
  (if (agda2-ast--stale-p)
      (agda2-ast--msg "AST map is stale; reload (C-c C-l).")
    ;; First press just snaps selection to node at point.
    (if (agda2-ast--ensure-current-at-point)
        nil
      (let* ((id agda2-ast--current))
        (if (null id)
            (agda2-ast--msg "No current node.")
          (let ((p (agda2-ast--parent id)))
            (if p
                (agda2-ast--select p t)  ; selection only; point stays
              (agda2-ast--msg "Already at top-level."))))))))

(defun agda2-ast-down (n)
  "Select the Nth child (1-based) of the current node, using point
to pick a default when possible; do not move point.
On first invocation when no node is selected or point is outside
the current node, just select the smallest node at point."
  (interactive "p")
  (setq n (max 1 n))
  (if (agda2-ast--stale-p)
      (agda2-ast--msg "AST map is stale; reload (C-c C-l).")
    ;; First press just snaps selection to node at point.
    (if (agda2-ast--ensure-current-at-point)
        nil
      (let* ((id   agda2-ast--current)
             (kids (and id (agda2-ast--children id))))
        (cond
         ((null id)
          (agda2-ast--msg "No current node."))
         ((null kids)
          (agda2-ast--msg "No children."))
         (t
          ;; If point lies in some child, prefer that child when N==1.
          (let* ((pos (point))
                 (child-in-pos (agda2-ast--child-containing-pos id pos))
                 (k (cond
                     ((and (= n 1) child-in-pos) child-in-pos)
                     (t (nth (1- n) kids)))))
            (if k
                (agda2-ast--select k t) ; selection only; point stays
              (agda2-ast--msg "No such child: %d" n)))))))))

;;;; Sideways helpers (walk up the tree when no sibling exists)

(defun agda2-ast--ancestor-sibling (id dir)
  "Return the sibling of ID in direction DIR, walking up through ancestors.
DIR must be \\='next or \\='prev. If ID has no sibling in DIR, try the parent;
if that has no sibling, continue with its parent, and so on. At the top level,
use `agda2-ast--tops' as the sibling list. Return a node id or nil."
  (let ((cur id) (res nil))
    (while (and cur (null res))
      (let ((p (agda2-ast--parent cur)))
        (if p
            ;; Try among parent's children.
            (let* ((sib (agda2-ast--children p))
                   (idx (cl-position cur sib)))
              (setq res
                    (pcase dir
                      ('next (and idx (< (1+ idx) (length sib))
                                  (nth (1+ idx) sib)))
                      ('prev (and idx (> idx 0)
                                  (nth (1- idx) sib)))))
              (setq cur p)) ; ascend
          ;; cur is a root: try among top-level roots, then stop
          (let* ((roots agda2-ast--tops)
                 (idx   (cl-position cur roots)))
            (setq res
                  (pcase dir
                    ('next (and idx (< (1+ idx) (length roots))
                                (nth (1+ idx) roots)))
                    ('prev (and idx (> idx 0)
                                (nth (1- idx) roots)))))
            (setq cur nil))))) ; stop after checking roots
    res))

(defun agda2-ast-next ()
  "Select next sibling (or next at some ancestor level), and move point.
On first invocation when no node is selected or point lies outside
the current node, just select the smallest node at point."
  (interactive)
  (if (agda2-ast--stale-p)
      (agda2-ast--msg "AST map is stale; reload (C-c C-l).")
    ;; First press just snaps selection to node at point.
    (if (agda2-ast--ensure-current-at-point)
        nil
      (let* ((id   agda2-ast--current)
             (cand (and id (agda2-ast--ancestor-sibling id 'next))))
        (cond
         ((null id)
          (agda2-ast--msg "No current node."))
         (cand
          (agda2-ast--select cand t)
          ;; lateral navigation moves point to end of node
          (let* ((pr (agda2-ast--to-buffer-pos cand))
                 (e  (cdr pr)))
            (goto-char e)))
         (t
          (agda2-ast--msg "No next sibling at any ancestor level.")))))))

(defun agda2-ast-prev ()
  "Select previous sibling (or previous at some ancestor level), and move point.
On first invocation when no node is selected or point lies outside
the current node, just select the smallest node at point."
  (interactive)
  (if (agda2-ast--stale-p)
      (agda2-ast--msg "AST map is stale; reload (C-c C-l).")
    ;; First press just snaps selection to node at point.
    (if (agda2-ast--ensure-current-at-point)
        nil
      (let* ((id   agda2-ast--current)
             (cand (and id (agda2-ast--ancestor-sibling id 'prev))))
        (cond
         ((null id)
          (agda2-ast--msg "No current node."))
         (cand
          (agda2-ast--select cand t)
          ;; lateral navigation moves point to end of node
          (let* ((pr (agda2-ast--to-buffer-pos cand))
                 (e  (cdr pr)))
            (goto-char e)))
         (t
          (agda2-ast--msg "No previous sibling at any ancestor level.")))))))

;;;; Minor mode & keys

(defvar agda2-ast-navigation-mode-map
  (let ((m (make-sparse-keymap)))
    (define-key m (kbd "C-c C-a .") #'agda2-ast-select-at-point)
    (define-key m (kbd "C-c C-a u") #'agda2-ast-up)
    (define-key m (kbd "C-c C-a d") #'agda2-ast-down)
    (define-key m (kbd "C-c C-a n") #'agda2-ast-next)
    (define-key m (kbd "C-c C-a p") #'agda2-ast-prev)
    ;; Arrow duplicates while the mode is active:
    (define-key m (kbd "M-<up>")    #'agda2-ast-up)
    (define-key m (kbd "M-<down>")  #'agda2-ast-down)
    (define-key m (kbd "M-<left>")  #'agda2-ast-prev)
    (define-key m (kbd "M-<right>") #'agda2-ast-next)
    m)
  "Keymap for `agda2-ast-navigation-mode'.")

;;;###autoload
(define-minor-mode agda2-ast-navigation-mode
  "Navigate Agda code by AST nodes (parent/child/siblings)."
  :lighter " AST"
  :keymap agda2-ast-navigation-mode-map
  (unless agda2-ast-navigation-mode
    (when (overlayp agda2-ast--overlay)
      (delete-overlay agda2-ast--overlay)
      (setq agda2-ast--overlay nil))
    (agda2-ast--clear-child-overlays)))

;;;; Frontend entry point (called by the Agda backend)

;;;###autoload
(defun agda2-ast-map-action (positions tops nodes)
  "Entry point called from Agda's Emacs serializer.
Expected shape:
  (agda2-ast-map-action POSITIONS TOPS NODES)
where
  POSITIONS is \\='codepoint or \\='line-col,
  TOPS      is a list of root node ids,
  NODES     is a list of (ID KIND BEG END (CHILD ...))."
  (unless (derived-mode-p 'agda2-mode)
    (agda2-ast--msg "Ignoring AST map outside agda2-mode."))
  (agda2-ast--ingest positions tops nodes))

(provide 'agda2-ast)
;;; agda2-ast.el ends here
