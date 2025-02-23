mkdir -p ~/.config/common-lisp/source-registry.conf.d/
CURRENT_DIR=`pwd`
SYSTEM_NAME=ex-caveman
echo '(:tree "'$CURRENT_DIR'/")' > ~/.config/common-lisp/source-registry.conf.d/$SYSTEM_NAME.conf