(defsystem "ex-caveman-test"
  :defsystem-depends-on ("prove-asdf")
  :author "The author"
  :license ""
  :depends-on ("ex-caveman"
               "prove")
  :components ((:module "tests"
                :components
                ((:test-file "ex-caveman"))))
  :description "Test system for ex-caveman"
  :perform (test-op (op c) (symbol-call :prove-asdf :run-test-system c)))
