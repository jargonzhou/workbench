(in-package :com.spike.cl.demo)

(defun hello-world ()
  (write-line "hello, demo!")
  ; use inner package functions
  (hello-inner))

(defun add (m n)
  (+ m n))