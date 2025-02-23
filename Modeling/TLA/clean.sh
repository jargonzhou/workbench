echo "Delete TLA+: *.out *.old states"
find . -name '*.out' -type f -delete
find . -name '*.old' -type f -delete
find . -depth -name 'states' -type d -print -exec rm -r {} + 
find . -name 'csv-out.csv' -type f -delete