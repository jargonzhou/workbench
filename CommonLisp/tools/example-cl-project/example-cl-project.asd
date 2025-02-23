(defsystem "example-cl-project"
  :version "0.0.1"
  :author ""
  :license ""
  :depends-on ()
  :components ((:module "src"
                :components
                ((:file "main"))))
  :description ""
  :in-order-to ((test-op (test-op "example-cl-project/tests"))))

(defsystem "example-cl-project/tests"
  :author ""
  :license ""
  :depends-on ("example-cl-project"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main"))))
  :description "Test system for example-cl-project"
  :perform (test-op (op c) (symbol-call :rove :run c)))
