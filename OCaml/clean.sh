echo "Delete OCaml: _build"
find . -depth -name '_build' -type d -print -exec rm -r {} + 