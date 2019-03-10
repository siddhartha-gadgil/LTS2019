for file in *.idr
do
  echo "checking $file"
  idris --check --package contrib "$file"
done
