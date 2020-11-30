;;; agda2-queue.el --- Simple FIFO character queues.
;; SPDX-License-Identifier: MIT License

(defun agda2-queue-empty ()
  "Creates a new empty FIFO character queue.
Queues are represented as pairs. The car contains the queue. If
the queue is empty, then the cdr contains the symbol nil, and
otherwise it points to the queue's last cons-cell."
  (cons nil nil))

(defun agda2-queue-is-prefix-of (prefix queue)
  "Returns a non-nil result iff the string PREFIX is a prefix of QUEUE.
Linear in the length of PREFIX."
  (let ((queue  (car queue))
        (prefix (append prefix nil)))
    (while (and (consp queue) (consp prefix)
                (equal (car queue) (car prefix)))
      (pop queue)
      (pop prefix))
    (null prefix)))

(defun agda2-queue-enqueue (queue string)
  "Adds the characters in STRING to the end of QUEUE.
This function updates QUEUE destructively, and is linear in the
length of STRING."
  (let ((chars (append string nil)))
    (when (consp chars)
      (if (null (cdr queue))
          (setcar queue chars)
        (setcdr (cdr queue) chars))
      (setcdr queue (last chars))))
  queue)

(defun agda2-queue-from-string (string)
  "Creates a new FIFO containing the characters in STRING.
Linear in the length of STRING."
  (agda2-queue-enqueue (agda2-queue-empty) string))

(defun agda2-queue-to-string (queue)
  "Constructs a string containing all the characters in QUEUE.
Linear in the length of QUEUE."
  (concat "" (car queue)))

(provide 'agda2-queue)
