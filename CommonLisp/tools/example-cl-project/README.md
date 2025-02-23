# Getting started

## Creating a new project

Skaffold:

```lisp
✗ rlwrap sbcl
* (ql:quickload "cl-project")

* (cl-project:make-project #P"./example-cl-project")
writing ./example-cl-project/example-cl-project.asd
writing ./example-cl-project/README.org
writing ./example-cl-project/README.markdown
writing ./example-cl-project/.gitignore
writing ./example-cl-project/src/main.lisp
writing ./example-cl-project/tests/main.lisp
T
* (exit)
```

## Load: `asdf:load-asd`

```lisp
✗ cd example-cl-project
✗ ls
README.markdown        README.org             example-cl-project.asd src                    tests
✗ rlwrap sbcl  
* (asdf:load-asd "[/absolute-path-to]/example-cl-project.asd")
#<ASDF/FIND-SYSTEM:DEFINE-OP >
#<ASDF/PLAN:SEQUENTIAL-PLAN {1002F49433}>
* (ql:quickload "example-cl-project")
To load "example-cl-project":
  Load 1 ASDF system:
    example-cl-project
; Loading "example-cl-project"
[package example-cl-project]
("example-cl-project")
* (in-package :example-cl-project)
#<PACKAGE "EXAMPLE-CL-PROJECT">
* (hello)

"Hello from example CL-Project." 
"Hello from example CL-Project."
```

## Load: `asdf:load-system`

```shell
mkdir -p ~/.config/common-lisp/source-registry.conf.d/
CURRENT_DIR=`pwd`
SYSTEM_NAME=example-cl-project
echo '(:tree "'$CURRENT_DIR'/")' > ~/.config/common-lisp/source-registry.conf.d/$SYSTEM_NAME.conf
```

```lisp
✗ rlwrap sbcl 
* (asdf:load-system "example-cl-project")
T
* (in-package :example-cl-project)
#<PACKAGE "EXAMPLE-CL-PROJECT">
* (hello)

"Hello from example CL-Project." 
"Hello from example CL-Project."
```

## Tests: `asdf:test-system`

```lisp
* (asdf:test-system "example-cl-project")

Testing System example-cl-project/tests

;; testing 'example-cl-project/tests/main'
test-target-1
  should (= 1 1) to be true
    ✓ Expect (= 1 1) to be true.

✓ 1 test completed

Summary:
  All 1 test passed.
T
```

### errors when running tests

```lisp
* (asdf:test-system "example-cl-project")
; compiling file "~/quicklisp/dists/quicklisp/software/dissect-20231021-git/backend/sbcl.lisp" (written 18 AUG 2024 10:54:10 AM):
; 
; caught ERROR:
;   READ error during COMPILE-FILE:
;   
;     Lock on package SB-DI violated when interning DEBUG-VAR-INFO while in package
;     DISSECT.
;   See also:
;     The SBCL Manual, Node "Package Locks"
;   
;     (in form starting at line: 38, column: 0, position: 1539)

; compilation aborted after 0:00:00.034

debugger invoked on a UIOP/LISP-BUILD:COMPILE-FILE-ERROR in thread
#<THREAD tid=775 "main thread" RUNNING {1003F90143}>:
  COMPILE-FILE-ERROR while
  compiling #<CL-SOURCE-FILE "dissect" "backend" "sbcl">

Type HELP for debugger help, or (SB-EXT:EXIT) to exit from SBCL.

; unlock!!!
* (sb-ext:unlock-package :sb-di)
T
* (asdf:test-system "example-cl-project")
Testing System example-cl-project/tests

;; testing 'example-cl-project/tests/main'
test-target-1
  should (= 1 1) to be true
    ✓ Expect (= 1 1) to be true.

✓ 1 test completed

Summary:
  All 1 test passed.
```