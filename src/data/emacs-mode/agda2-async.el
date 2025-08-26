;; -*- lexical-binding: t -*-
;; agda2-abbrevs.el --- Handling for asynchronous queries
;; SPDX-License-Identifier: MIT License

;;; Commentary:

;;; Code:

(require 'cl-lib)

(defvar-local agda2--async-requests (make-hash-table)
  "Variable associating in-flight asynchronous requests to their callbacks.")

(defun agda2--defer (okay &optional err)
  "Register OKAY as a callback pair for asynchronous execution. If
given, ERR will be called when Agda fails the callback instead.

Returns an identifier suitable for use as a QueryId in Interactions that
take a callback."
  (let ((id (random (expt 2 24))))
    (puthash id (cons okay (or err (lambda ()))) agda2--async-requests)
    id))

(defmacro agda2-async (bindings &rest body)
  "Execute a series of asynchronous commands, according to BINDINGS, and
execute BODY after each returns. Note: the semantics of this are
\"monadic\", not \"applicative\", so a subsequent binding will only be
dispatched when the previous binding returns.

Each form in BINDINGS should be a list of form

  (ARGLIST COMMAND :args COMMAND-ARGS :else FAIL-CONTINUATION)

The ARGLIST a complete CL argument list, c.f. `cl-destructuring-bind'.
The FAIL-CONTINUATION is optional, but, if given, will be invoked if
execution of *this* command fails (again, note: if a command fails, no
subsequent commands will be dispatched).

The COMMAND and COMMAND-ARGS should construct a value suitable for
invoking `agda2-go'. The Haskell constructor for COMMAND should take a
QueryId as its *first* argument.
"
  (cl-labels
    ; Dispatch a single command
    ((async-one ((args cmd &key ((:args cargs)) (else '(lambda ()))) &rest body)
       (let ((cbid (cl-gensym)) (argn (cl-gensym)))
         `(let ((,cbid (agda2--defer
                         (lambda (&rest ,argn)
                           (cl-destructuring-bind ,args ,argn
                             ,@body))
                         ,else)))
             (apply #'agda2-go nil nil 'not-so-busy 't ,cmd
               (format "%d" ,cbid)
               ,cargs)
             t)))

     ; Dispatch a bunch of them
     (async-loop (bindings body)
       (if (consp bindings)
         (async-one (car bindings)
           (async-loop (cdr bindings) body))
         `(progn ,@body t))))

    (async-loop bindings body)))

(defun agda2-invoke-callback (id &rest args)
  "Invoke the success continuation for the async command with identifier
ID, with the given ARGS, and drop it from the `agda2--async-requests'
table.

Called from Haskell."
  (let ((callback (gethash id agda2--async-requests)))
    (remhash id agda2--async-requests)
    (apply (car callback) args)))

(defun agda2-drop-callback (id)
  "Invoke the failure continuation for the async command with identifier
ID, and drop it from the `agda2--async-requests' table.

Called from Haskell."
  (let ((callback (gethash id agda2--async-requests)))
    (remhash id agda2--async-requests)
    (funcall (cdr callback))))

(defun agda2-async-thunk (cmd &rest cmd-args)
  "Asynchronously dispatch the execution of CMD, with arguments
CMD-ARGS, and return a function that can be used to either probe for
its completion or wait on it.

If execution of CMD fails on the Agda side, the waiting function signals
\='agda2-async-wait-failed if the failured happening during waiting, or
any time in the future if its polled again."
  (let (done)
    (cl-labels
      ;; Abstracting over the common part of handling the output: if
      ;; there's an error, raise the signal, on success return the
      ;; command result, otherwise (still running) return nil.
      ((report () (pcase done
         (`(error)        (signal 'agda2-async-wait-failed))
         (`(okay . ,retv) retv)
         (_               nil)))

       ;; Waiting loop: just accept-process-output until we're either
       ;; done or the user types something.
       (wait ()
         (let ((tag (cl-gensym)))
           (catch tag (while-no-input
             (accept-process-output nil 10)
             (when (report) (throw tag t))))))

       ;; The actual thunk takes a keyword argument `:wait` if you want
       ;; to try waiting for a bit, otherwise it just reports on the
       ;; status.
       (poll (&key (wait nil))
         (when (and wait (not done)) (wait))
         (report)))

      ;; Actually dispatch the command. On return just set the local
      ;; 'done'.
      (agda2-async
        ((cmd-ret cmd
          :args cmd-args
          :else (lambda () (setq done '(error)))))
        (setq done (cons 'okay cmd-ret)))

      #'poll)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'agda2-async)
;;; agda2-highlight.el ends here
