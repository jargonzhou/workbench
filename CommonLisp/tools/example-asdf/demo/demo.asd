(defpackage :com.spike.cl.demo-system
  (:use :cl :asdf :uiop))
(in-package :com.spike.cl.demo-system)

(defsystem demo
  :name "demo"
  :author "zhoujiagen"
  :version "1.0"
  :maintainer "zhoujiagen"
  :licence "MIT"
  :description "<description>"
  :long-description "<long-description>"
  :components
  ((:file "packages" :depends-on (inner))
   (:file "demo" :depends-on ("packages"))
   ; modules
   (:module inner
            :components ((:file "inner" :depends-on ("packages"))
                         (:file "packages"))))
  :in-order-to ((test-op (test-op demo/test))))

(defsystem demo/test
  :depends-on (demo "fiveam")
  :pathname "t/"
  :components
  ((:file "tests"))
  :perform (test-op (o c)
                    (symbol-call :fiveam :run! 'demo-suite)))
