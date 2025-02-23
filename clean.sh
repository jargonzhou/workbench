echo "Delete *.pyc..."
find . -name '*.pyc' -type f -delete

echo "Delete .ipynb_checkpoints..."
find . -depth -name '.ipynb_checkpoints' -type d -print -exec rm -r {} + 
echo "Delete __pycache__..."
find . -depth -name '__pycache__' -type d -print -exec rm -r {} + 
echo "Delete .venv..."
find . -depth -name '.venv' -type d -print -exec rm -r {} + 


chmod +x CommonLisp/clean.sh
CommonLisp/clean.sh

chmod +x Java/clean.sh
Java/clean.sh

chmod +x Scala/clean.sh
Scala/clean.sh

chmod +x Compiler/clean.sh
Compiler/clean.sh

chmod +x DataEngineering/clean.sh
DataEngineering/clean.sh

chmod +x OCaml/clean.sh
OCaml/clean.sh

echo "Done"
