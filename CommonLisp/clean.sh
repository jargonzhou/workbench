echo "Delete common-lisp-jupyter"
# find . -name 'kernel-*.log' -type f -delete
find . -depth -name 'common-lisp-jupyter' -type d -print -exec rm -r {} +

echo "Delete alive fasl"
find . -name '*.fasl' -type f -delete
find . -name 'tmp.lisp' -type f -delete


