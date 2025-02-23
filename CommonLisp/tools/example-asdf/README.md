# ASDF

```shell
├── demo.asd            # ASDF system definition
├── demo.lisp
├── inner               # inner package
│   ├── inner.lisp
│   └── packages.lisp
├── packages.lisp       # package
└── t
    └── tests.lisp      # tests
```

Load `demo` system:
```shell
✗ CURRENT_DIR=`pwd`       
✗ SYSTEM_NAME=demo
✗ echo '(:tree "'$CURRENT_DIR'/")' > ~/.config/common-lisp/source-registry.conf.d/$SYSTEM_NAME.conf
```

or using `load-asd`: 
```lisp
(asdf:load-asd (uiop:subpathname (uiop:getcwd) "demo.asd"))
```

```lisp
✗ rlwrap sbcl 
* (asdf:load-system :demo)
* (in-package :com.spike.cl.demo)
#<PACKAGE "COM.SPIKE.CL.DEMO">
* (hello-world)
hello, demo!
hello, inner!
"hello, inner!"
```

Tests with [FiveAM](https://github.com/lispci/fiveam):
```shell
* (asdf:test-system "demo")

* (asdf:test-system "demo")
Running test SIMPLE-MATHS .
 Did 1 check.
    Pass: 1 (100%)
    Skip: 0 ( 0%)
    Fail: 0 ( 0%)


Running test ADDTEST .
 Did 1 check.
    Pass: 1 (100%)
    Skip: 0 ( 0%)
    Fail: 0 ( 0%)

 Didn't run anything...huh?
T
```