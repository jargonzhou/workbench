;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Constructs in 'On Lisp'.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defpackage :on-lisp
  (:use :cl)
  (:nicknames "on-lisp")
  (:export :hello))

(in-package :on-lisp)

(defun hello ()
  (print "Hello, On Lisp!"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 2. Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; Defining Functions
;;;

(defun double (x) (* x 2))
; same
(setf (symbol-function 'double%)
  #'(lambda (x) (* x 2)))
(export 'double%)

;;;
;;; Closure
;;;

(defun make-adder (n)
  #'(lambda (x) (+ x n)))

;;;
;;; Local Functions
;;;

;;; count occurences of [obj] in each list in [lsts].
(defun count-instances (obj lsts)
  (labels ((instances-in (lst)
                         (if (consp lst)
                             (+ (if (eq (car lst) obj) 1 0)
                                (instances-in (cdr lst)))
                             0)))
    (mapcar #'instances-in lsts)))
(export 'count-instances)

;;;
;;; Compilation
;;;

;;; inline
(defun 50th (lst)
  (proclaim '(inline 50th))
  (nth 49 lst))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4. Utility Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; Mapping
;;;

;;; map [fn] from [a] to [b].
(defun mapa-b (fn a b &optional (step 1))
  (do ((i a (+ i step))
       (result nil))
      ((> i b) (nreverse result))
    (push (funcall fn i) result)))
(export 'mapa-b)

(defun map0-n (fn n)
  (mapa-b fn 0 n))
(export 'map0-n)

(defun map1-n (fn n)
  (mapa-b fn 1 n))
(export 'map1-n)

;;; map [fn] from [start], next value with [succ-fn], stop with [test-fn].
(defun map-> (fn start test-fn succ-fn)
  (do ((i start (funcall succ-fn i))
       (result nil))
      ((funcall test-fn i) (nreverse result))
    (push (funcall fn i) result)))
(export 'map->)

;;; mapcar [fn] on list of lists, return appended list.
(defun mappend (fn &rest lsts)
  (apply #'append (apply #'mapcar fn lsts)))
(export 'mapapend)

;;; map fn on list of lists, return flatted list.
(defun mapcars (fn &rest lsts)
  (let ((result nil))
    (dolist (lst lsts)
      (dolist (obj lst)
        (push (funcall fn obj) result)))
    (nreverse result)))
(export 'mapcars)

;;; recursive mapcar.
(defun rmapcar (fn &rest args)
  (if (some #'atom args)
      (apply fn args)
      (apply #'mapcar
          #'(lambda (&rest args)
              (apply #'rmapcar fn args))
        args)))
(export 'rmapcar)

;;;
;;; I/O
;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 11. Classic Macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; Iteration
;;;
(defmacro while (test &body body)
  `(do ()
       ((not ,test))
     ,@body))
(export 'while)

(defmacro till (test &body body)
  `(do ()
       (,test)
     ,@body))
(export 'till)

(defmacro for ((var start stop) &body body)
  (let ((gstop (gensym)))
    `(do ((,var ,start (1+ ,var))
          (,gstop ,stop))
         ((> ,var ,gstop))
       ,@body)))
(export 'for)
