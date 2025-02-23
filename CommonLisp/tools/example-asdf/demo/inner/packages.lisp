(in-package :common-lisp-user)

;;; An inner package
(defpackage :com.spike.cl.demo.inner
  (:use :common-lisp)
  (:export :hello-inner))
