echo "Delete Java: *.class"
find . -name '*.class' -type f -delete
# find . -depth -name 'target' -type d -print -exec rm -r {} + 