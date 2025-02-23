(in-package :common-lisp-user)

(defpackage :com.spike.cl.demo
  (:use :common-lisp
        :com.spike.cl.demo.inner ; use inner package
        )
  (:export 
  :hello-world
  :add))
