;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Common utilities when hacking Common Lisp.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defpackage "CL-COMMON"
  (:use :cl)
  (:nicknames "cl-common")
  (:export
   #:hello
   #:hello-macro
   #:dump-symbol))

(in-package :cl-common)

(defun hello ()
  "Demo function: hello."
  (print "Hello, Common!"))


(defmacro hello-macro ()
  "Demo macro: hello-macro."
  `(hello))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Symbols
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ref: SYMBOL-FUNCTION
(defun symbol-function-or-nil (symbol)
  (if (and (fboundp symbol)
           (not (macro-function symbol))
           (not (special-operator-p symbol)))
      (symbol-function symbol)
      nil))
(export 'symbol-function-or-nil)

(defun dump-symbol (sym)
  "Dump symbols."
  (if (symbolp sym)
      (cond
       ;; macro
       ((macro-function sym)
         (format t "~A [MACRO]~%" sym)
         (if (documentation sym 'function)
             (format t "~t\"~A\"" (documentation sym 'function))
             (format t "~t~A" (type-of sym))))
       ;; function
       ((and (fboundp sym)
             (not (macro-function sym))
             (not (special-operator-p sym)))
         (format t "~A [FUNCTION]~%" sym)
         (if (documentation sym 'function)
             (format t "~t\"~A\"" (documentation sym 'function))
             (format t "~t~A" (type-of (symbol-function sym)))))
       (t (format t "~A~%" sym))))
  (format t "~%~%"))
