echo "Delete .antlr .antlrgen"
find . -depth -name '.antlr' -type d -print -exec rm -r {} + 
find . -depth -name '.antlrgen' -type d -print -exec rm -r {} + 
find . -name '*.jar' -type f -delete